{-# language DeriveFunctor #-}
{-# language FlexibleContexts #-}
{-# language MultiParamTypeClasses #-}
{-# language TemplateHaskell #-}

import Control.Lens
import Data.Foldable
import Data.Bifunctor
import Control.Monad.Error.Lens
import Control.Monad.Except
import Control.Monad.Free
import Control.Monad.Fresh
import Control.Monad.Trans
import Control.Monad.Reader
import Control.Monad.State
import Data.Functor
import Data.List.NonEmpty (NonEmpty(..))
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe
import System.Console.Haskeline hiding (catches)
import System.Directory
import System.Exit
import System.FilePath
import System.IO
import Text.PrettyPrint

import qualified Phil.AST.Definitions as L
import qualified Phil.AST.Expr as L
import Phil.AST (toCore, toCoreExpr)
import qualified Phil.Core.AST.Binding as C
import qualified Phil.Core.AST.Definitions as C
import Phil.Core.AST.Literal
import Phil.Core.AST.Identifier
import qualified Phil.Core.AST.Expr as C
import Phil.Core.AST.Types
import Phil.Core.AST.Pattern
import Phil.Core.Kinds
import Phil.Lexer
import Phil.Lexer.LexError
import Phil.Parser
import Phil.Parser.ParseError
import Phil.Sugar (desugar, desugarExpr)
import Phil.Sugar.SyntaxError
import Phil.Typecheck
import Phil.Typecheck.TypeError
import Phil.Typeclasses

data Value
  = VLiteral Literal
  | VClosure (Map Identifier Value) Identifier C.Expr
  | VProduct Identifier [Value]
  | VPointer C.Expr
  | VError String
  deriving (Eq, Show)

class HasSymbolTable s where
  symbolTable :: Lens' s (Map Identifier Value)

data InterpreterState
  = InterpreterState
    { _interpSymbolTable :: Map Identifier Value
    , _interpKindTable :: Map Identifier Kind
    , _interpTypesignatures :: Map Identifier TypeScheme
    , _interpContext :: Map Identifier ContextEntry
    , _interpTcContext :: [TypeclassEntry C.Expr]
    }

makeClassy ''InterpreterState

initialInterpreterState
  = InterpreterState
  { _interpSymbolTable = M.empty
  , _interpKindTable = M.empty
  , _interpTypesignatures = M.empty
  , _interpContext = M.empty
  , _interpTcContext = []
  }

instance HasSymbolTable InterpreterState where
  symbolTable = interpreterState . interpSymbolTable

instance HasContext InterpreterState where
  context = interpreterState . interpContext

instance HasTypesignatures InterpreterState where
  typesignatures = interpreterState . interpTypesignatures

instance HasKindTable InterpreterState where
  kindTable = interpreterState . interpKindTable

instance HasTcContext C.Expr InterpreterState where
  tcContext = interpreterState . interpTcContext

data InterpreterError
  = NotBound String
  | RuntimeError String
  | InterpreterTypeError TypeError
  | InterpreterKindError KindError
  | InterpreterLexError LexError
  | InterpreterParseError ParseError
  | InterpreterSyntaxError SyntaxError
  deriving Show

makeClassyPrisms ''InterpreterError

instance AsTypeError InterpreterError where
  _TypeError = _InterpreterTypeError . _TypeError

instance AsKindError InterpreterError where
  _KindError = _InterpreterKindError . _KindError

instance AsParseError InterpreterError where
  _ParseError = _InterpreterParseError . _ParseError

instance AsLexError InterpreterError where
  _LexError = _InterpreterLexError . _LexError

instance AsSyntaxError InterpreterError where
  _SyntaxError = _InterpreterSyntaxError . _SyntaxError

tryAll :: MonadError e m => m a -> [m a] -> m a
tryAll e [] = e
tryAll e (e':es) = e `catchError` const (tryAll e' es)

withBinding ::
  ( MonadReader (Map Identifier Value) m
  , AsInterpreterError e
  , MonadError e m
  )
  => C.Binding C.Expr -> m a -> m a
withBinding (C.Binding name expr) m = do
  expr' <- eval expr
  local (M.insert name expr') m

eval ::
  ( MonadReader (Map Identifier Value) m
  , AsInterpreterError e
  , MonadError e m
  )
  => C.Expr
  -> m Value
eval (C.Lit lit) = pure $ VLiteral lit
eval (C.Error message) = throwError $ _RuntimeError # message
eval (C.Id name) = do
  maybeExpr <- view $ at name
  case maybeExpr of
    Just (VPointer expr) -> eval expr
    Just value -> pure value
    Nothing -> do
      table <- ask
      throwError $ _NotBound # name
eval (C.Abs name output) = VClosure <$> ask <*> pure name <*> pure output
eval (C.App func input) = do
  func' <- eval func
  case func' of
    VClosure env name output -> do
      input' <- eval input
      local (M.insert name input' . const env) $ eval output
    VPointer expr -> eval (C.App expr input)
    _ -> error $ "Tried to apply a value to a non-function expression: " ++ show func'
eval (C.Let binding rest) = withBinding binding $ eval rest
eval (C.Rec (C.Binding name value) rest) = local (M.insert name $ VPointer value) $ eval rest
eval c@(C.Case var (b :| bs)) = do
  var' <- eval var
  tryBranch var' b bs
  where
    inexhaustiveCase = VError "Inexhaustive case expression"
    tryBranch val (PatId name,b) [] = local (M.insert name val) $ eval b
    tryBranch val (PatWildcard,b) [] = eval b
    tryBranch val (PatCon con args,b) [] = case val of
      VProduct name vals
        | con == name -> local (flip (foldr (uncurry M.insert)) (zip args vals)) $ eval b
        | otherwise  -> return inexhaustiveCase
      _ -> error "Structure pattern in branch but matching on non-structured value"
    tryBranch val (PatLit l,b) [] = case val of
        VLiteral l'
          | l == l' -> eval b
          | otherwise -> return inexhaustiveCase
        _ -> error "Literal in branch but matching on non-literal value"
    tryBranch val br (b:bs) = do
      res <- tryBranch val br []
      case res of
        VError _ -> tryBranch val b bs
        _ -> pure res
eval (C.Prod name args) = VProduct name <$> traverse eval args

data ReplF a
  = Read (String -> a)
  | Previous (String -> a)
  | PrintLine String a
  | PrintString String a
  | Quit
  deriving Functor

type Repl = Free ReplF

readLine :: MonadFree ReplF m => m String
readLine = liftF $ Read id

printLine :: MonadFree ReplF m => String -> m ()
printLine str = liftF $ PrintLine str ()

evaluate ::
  ( MonadFresh m
  , HasKindTable s
  , HasContext s
  , HasSymbolTable s
  , AsTypeError e
  , AsKindError e
  , AsInterpreterError e
  , MonadError e m
  , MonadState s m
  ) => L.Expr
  -> m Value
evaluate expr = do
  ctxt <- use context
  let expr' = desugarExpr expr
  runWithContext ctxt expr'
  table <- use symbolTable
  runReaderT (eval $ toCoreExpr expr') table

define ::
  ( MonadFresh m
  , HasKindTable s
  , HasSymbolTable s
  , HasContext s
  , HasTypesignatures s
  , HasTcContext C.Expr s
  , AsInterpreterError e
  , AsTypeError e
  , AsKindError e
  , AsSyntaxError e
  , MonadError e m
  , MonadState s m
  )
  => L.Definition
  -> m ()
define def = do
  (exprs, _) <- checkDefinition =<< desugar def
  exprs' <- runReaderT (traverse eval exprs) =<< use symbolTable
  symbolTable %= M.union exprs'

typeCheck ::
  ( MonadFresh m
  , HasKindTable s
  , HasContext s
  , AsTypeError e
  , AsKindError e
  , MonadError e m
  , MonadState s m
  )
  => L.Expr
  -> m TypeScheme
typeCheck expr = do
  ctxt <- use context
  snd <$> runWithContext ctxt (desugarExpr expr)

kindOf ::
  ( HasKindTable s
  , AsKindError e
  , MonadError e m
  , MonadState s m
  )
  => Identifier
  -> m Kind
kindOf name = fmap snd $ runInferKind (TyCon $ TypeCon name) =<< use kindTable

quit :: MonadFree ReplF m => m a
quit = liftF Quit

showNestedValue :: Value -> String
showNestedValue v@(VProduct _ (_:_)) = "(" ++ showValue v ++ ")"
showNestedValue v = showValue v

showValue :: Value -> String
showValue (VLiteral lit) = showLiteral lit
showValue VClosure{} = "<Function>"
showValue (VError message) = "Runtime Error: " ++ message
showValue (VProduct name args) = unwords . (:) name $ fmap showNestedValue args

repl ::
  ( MonadFresh m
  , HasKindTable s
  , HasContext s
  , HasTypesignatures s
  , HasSymbolTable s
  , HasTcContext C.Expr s
  , MonadFree ReplF m
  , AsLexError e
  , AsParseError e
  , AsTypeError e
  , AsKindError e
  , AsSyntaxError e
  , AsInterpreterError e
  , MonadError e m
  , MonadState s m
  )
  => m ()
repl = do
  input <- readLine
  printLine ""
  flip catches handlers $ do
    output <- case input of
      ':':'q':_ -> quit
      ':':'t':' ':rest -> do
        toks <- tokenize rest
        expr <- parseExpression toks
        showTypeScheme <$> typeCheck (desugarExpr expr)
      ':':'k':' ':rest -> do
        kind <- kindOf rest
        pure $ unwords [rest, ":", showKind kind]
      rest -> do
        toks <- tokenize rest
        input <- parseExprOrData toks
        case input of
          ReplExpr expr -> showValue <$> evaluate (desugarExpr expr)
          ReplDef dat -> define dat $> ""
    printLine output
  printLine ""
  repl
  where
    handlers =
      [ handler _LexError $ printLine . render . lexErrorMsg
      , handler _ParseError $ printLine . render . parseErrorMsg
      , handler _TypeError $ printLine . render . typeErrorMsg
      , handler _KindError $ printLine . render . kindErrorMsg
      , handler _SyntaxError $ printLine . render . syntaxErrorMsg
      ]

replIO :: ReplF a -> InputT IO a
replIO (Read a) = a . fromMaybe "" <$> getInputLine "> "
replIO (PrintLine str a) = outputStrLn str $> a
replIO Quit = liftIO exitSuccess

main :: IO (Either InterpreterError ())
main = do
  tempDir <- getTemporaryDirectory
  runInputT defaultSettings
    { historyFile = Just $ tempDir </> "phi_history" } $
    foldFree replIO (runExceptT . runFreshT . flip evalStateT initialInterpreterState $ repl)
