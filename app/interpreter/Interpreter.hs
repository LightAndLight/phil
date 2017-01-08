{-# language DeriveFunctor #-}
{-# language FlexibleContexts #-}
{-# language TemplateHaskell #-}

import Control.Lens
import Data.Foldable
import Data.Bifunctor
import Control.Monad.Except
import Control.Monad.Free
import Control.Monad.Trans
import Control.Monad.Reader
import Control.Monad.State
import Data.Functor
import Data.List.NonEmpty (NonEmpty(..))
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe
import System.Console.Haskeline
import System.Directory
import System.Exit
import System.FilePath
import System.IO

import Lambda.Core.AST hiding (Definition, Expr)
import Lambda.Core.Kind
import qualified Lambda.Core.AST as C (Definition(..), Expr(..))
import qualified Lambda.Sugar as S (Definition(..), Expr(..), desugar, desugarExpr)
import Lambda.Core.Typecheck
import Lambda.Lexer
import Lambda.Parser

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
    , _interpContext :: Map Identifier TypeScheme
    , _interpFreshCount :: Int
    }

makeClassy ''InterpreterState

initialInterpreterState = InterpreterState M.empty M.empty M.empty M.empty 0

instance HasSymbolTable InterpreterState where
  symbolTable = interpreterState . interpSymbolTable

instance HasContext InterpreterState where
  context = interpreterState . interpContext

instance HasTypesignatures InterpreterState where
  typesignatures = interpreterState . interpTypesignatures

instance HasFreshCount InterpreterState where
  freshCount = interpreterState . interpFreshCount

instance HasKindTable InterpreterState where
  kindTable = interpreterState . interpKindTable

data InterpreterError
  = NotBound String
  | RuntimeError String
  | InterpreterTypeError TypeError
  | InterpreterLexError LexError
  | InterpreterParseError ParseError
  deriving Show

makeClassyPrisms ''InterpreterError

instance AsTypeError InterpreterError where
  _TypeError = _InterpreterTypeError . _TypeError

instance AsKindError InterpreterError where
  _KindError = _InterpreterTypeError . _KindError

instance AsParseError InterpreterError where
  _ParseError = _InterpreterParseError . _ParseError

instance AsLexError InterpreterError where
  _LexError = _InterpreterLexError . _LexError

tryAll :: MonadError e m => m a -> [m a] -> m a
tryAll e [] = e
tryAll e (e':es) = e `catchError` const (tryAll e' es)

withBinding ::
  ( MonadReader (Map Identifier Value) m
  , AsInterpreterError e
  , MonadError e m
  )
  => Binding -> m a -> m a
withBinding (Binding name expr) m = do
  expr' <- eval expr
  local (M.insert name expr') m

eval ::
  ( MonadReader (Map Identifier Value) m
  , AsInterpreterError e
  , MonadError e m
  )
  => C.Expr
  -> m Value
eval (Lit lit) = pure $ VLiteral lit
eval (Error message) = throwError $ _RuntimeError # message
eval (Id name) = do
  maybeExpr <- view $ at name
  case maybeExpr of
    Just (VPointer expr) -> eval expr
    Just value -> pure value
    Nothing -> do
      table <- ask
      throwError $ _NotBound # name
eval (Abs name output) = VClosure <$> ask <*> pure name <*> pure output
eval (App func input) = do
  func' <- eval func
  case func' of
    VClosure env name output -> do
      input' <- eval input
      local (M.insert name input' . const env) $ eval output
    VPointer expr -> eval (App expr input)
    _ -> error $ "Tried to apply a value to a non-function expression: " ++ show func'
eval (Let binding rest) = withBinding binding $ eval rest
eval (Rec (Binding name value) rest) = local (M.insert name $ VPointer value) $ eval rest
eval c@(Case var (b :| bs)) = do
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
eval (Prod name args) = VProduct name <$> traverse eval args

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

printString :: MonadFree ReplF m => String -> m ()
printString str = liftF $ PrintString str ()

evaluate ::
  ( HasKindTable s
  , HasContext s
  , HasFreshCount s
  , HasSymbolTable s
  , AsTypeError e
  , AsInterpreterError e
  , MonadError e m
  , MonadState s m
  ) => C.Expr
  -> m Value
evaluate expr = do
  ctxt <- use context
  runWithContext ctxt expr
  table <- use symbolTable
  runReaderT (eval expr) table

define ::
  ( HasKindTable s
  , HasSymbolTable s
  , HasFreshCount s
  , HasContext s
  , HasTypesignatures s
  , AsInterpreterError e
  , AsTypeError e
  , AsKindError e
  , MonadError e m
  , MonadState s m
  )
  => S.Definition
  -> m ()
define def = do
  exprs <- checkDefinition $ S.desugar def
  exprs' <- runReaderT (traverse eval exprs) =<< use symbolTable
  symbolTable %= M.union exprs'

typeCheck ::
  ( HasKindTable s
  , HasContext s
  , HasFreshCount s
  , AsTypeError e
  , MonadError e m
  , MonadState s m
  )
  => C.Expr
  -> m TypeScheme
typeCheck expr = do
  freshCount .= 0
  ctxt <- use context
  runWithContext ctxt expr

kindOf ::
  ( HasKindTable s
  , AsKindError e
  , MonadError e m
  , MonadState s m
  )
  => Identifier
  -> m Kind
kindOf name = do
  table <- use kindTable
  snd <$> evalStateT (runReaderT (inferKind (TyCon $ TypeCon name)) table) (KindInferenceState 0)

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
  ( HasKindTable s
  , HasContext s
  , HasTypesignatures s
  , HasSymbolTable s
  , HasFreshCount s
  , MonadFree ReplF m
  , Show e
  , AsLexError e
  , AsParseError e
  , AsTypeError e
  , AsKindError e
  , AsInterpreterError e
  , MonadError e m
  , MonadState s m
  )
  => m ()
repl = flip catchError handleError $ do
  input <- readLine
  output <- case input of
    ':':'q':_ -> quit
    ':':'t':' ':rest -> do
      toks <- tokenize rest
      expr <- parseExpression toks
      showTypeScheme <$> typeCheck (S.desugarExpr expr)
    ':':'k':' ':rest -> do
      kind <- kindOf rest
      pure $ unwords [rest, ":", showKind kind]
    rest -> do
      toks <- tokenize rest
      input <- parseExprOrData toks
      case input of
        ReplExpr expr -> showValue <$> evaluate (S.desugarExpr expr)
        ReplDef dat -> define dat $> ""
  printLine output
  repl
  where
    handleError e = do
      printLine $ show e
      repl

replIO :: ReplF a -> InputT IO a
replIO (Read a) = a . fromMaybe "" <$> getInputLine "> "
replIO (PrintLine str a) = outputStrLn str >> outputStrLn "" $> a
replIO (PrintString str a) = do
  outputStr str
  -- liftIO $ hFlush stdout
  return a
replIO Quit = liftIO exitSuccess

main :: IO (Either InterpreterError ())
main = do
  tempDir <- getTemporaryDirectory
  runInputT defaultSettings
    { historyFile = Just $ tempDir </> "lambdai_history" } $ foldFree replIO (runExceptT . flip evalStateT initialInterpreterState $ repl)
