{-# language DeriveFunctor #-}
{-# language FlexibleContexts #-}
{-# language TemplateHaskell #-}

import Control.Lens
import Data.Foldable
import Data.Bifunctor
import Control.Monad.Except
import Control.Monad.Free
import Control.Monad.Trans
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
import qualified Lambda.Core.AST as C (Definition(..), Expr(..))
import qualified Lambda.Sugar as S (Definition(..), Expr(..), desugar, desugarExpr)
import Lambda.Core.Typecheck
import Lambda.Lexer
import Lambda.Parser

type SymbolTable = Map Identifier C.Expr

class HasSymbolTable s where
  symbolTable :: Lens' s (Map Identifier C.Expr)

data InterpreterState
  = InterpreterState
    { _interpSymbolTable :: Map Identifier C.Expr
    , _interpTypeTable :: Map Identifier Int
    , _interpContext :: Map Identifier TypeScheme
    , _interpFreshCount :: Int
    }

makeClassy ''InterpreterState

initialInterpreterState = InterpreterState M.empty M.empty M.empty 0

instance HasSymbolTable InterpreterState where
  symbolTable = interpreterState . interpSymbolTable

instance HasContext InterpreterState where
  context = interpreterState . interpContext

instance HasFreshCount InterpreterState where
  freshCount = interpreterState . interpFreshCount

instance HasTypeTable InterpreterState where
  typeTable = interpreterState . interpTypeTable

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

instance AsParseError InterpreterError where
  _ParseError = _InterpreterParseError . _ParseError

instance AsLexError InterpreterError where
  _LexError = _InterpreterLexError . _LexError

tryAll :: MonadError e m => m a -> [m a] -> m a
tryAll e [] = e
tryAll e (e':es) = e `catchError` const (tryAll e' es)

reduce ::
  ( HasSymbolTable s
  , MonadState s m
  , AsInterpreterError e
  , MonadError e m
  )
  => C.Expr
  -> m C.Expr
reduce (Error message) = throwError $ _RuntimeError # message
reduce (Id name) = do
  maybeExpr <- use (symbolTable . at name)
  case maybeExpr of
    Just expr -> return expr
    Nothing -> throwError $ _NotBound # name
reduce (App func input) = do
  func' <- reduce func
  input' <- reduce input
  case func' of
    Abs name output -> do
      symbolTable %= M.insert name input'
      reduce output
    _ -> error "Tried to apply a value to a non-function expression"
reduce (Let name expr rest) = do
  expr' <- reduce expr
  symbolTable %= M.insert name expr'
  reduce rest
reduce c@(Case var (b :| bs)) = do
  var' <- reduce var
  case var' of
    Id{} -> return c
    _ -> tryBranch var' b bs
  where
    inexhaustiveCase = Error "Inexhaustive case expression"
    tryBranch expr (PatId name,b) [] = do
      symbolTable %= M.insert name expr
      reduce b
    tryBranch expr (PatWildcard,b) [] = reduce b
    tryBranch expr (PatCon con args,b) [] = do
      expr' <- reduce expr
      case expr' of
        Prod name vals
          | con == name -> do
              for_ (zip args vals) $ \(a,v) -> symbolTable %= M.insert a v
              reduce b
          | otherwise  -> return inexhaustiveCase
        _ -> error "Structure pattern in branch but matching on non-structured value"
    tryBranch expr (PatLit l,b) [] = do
      expr' <- reduce expr
      return $ case expr' of
        Lit l'
          | l == l' -> b
          | otherwise -> inexhaustiveCase
        _ -> error "Literal in branch but matching on non-literal value"
    tryBranch expr br (b:bs) = do
      res <- tryBranch expr br []
      case res of
        Error _ -> tryBranch expr b bs
        _ -> reduce res
reduce (Prod name args) = Prod name <$> traverse reduce args
reduce expr = pure expr

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
  ( HasTypeTable s
  , HasContext s
  , HasFreshCount s
  , HasSymbolTable s
  , MonadFree ReplF m
  , AsTypeError e
  , AsInterpreterError e
  , MonadError e m
  , MonadState s m
  ) => C.Expr
  -> m C.Expr
evaluate expr = do
  ctxt <- use context
  runWithContext ctxt expr
  reduce expr

define ::
  ( HasTypeTable s
  , HasSymbolTable s
  , HasFreshCount s
  , HasContext s
  , MonadFree ReplF m
  , AsTypeError e
  , MonadError e m
  , MonadState s m
  )
  => S.Definition
  -> m ()
define def = do
  exprs <- checkDefinition $ S.desugar def
  symbolTable %= M.union exprs

typeCheck ::
  ( HasTypeTable s
  , HasContext s
  , HasFreshCount s
  , MonadFree ReplF m
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

quit :: MonadFree ReplF m => m a
quit = liftF Quit

nested :: Type -> String
nested ty@FunType{} = "(" ++ showType ty ++ ")"
nested ty@PolyType{} = "(" ++ showType ty ++ ")"
nested ty = showType ty

showType :: Type -> String
showType (TypeVar name) = name
showType (PrimType ty) = show ty
showType (FunType from to) = nested from ++ " -> " ++ showType to
showType (PolyType cons args) = cons ++ " " ++ unwords (fmap nested args)

showTypeScheme :: TypeScheme -> String
showTypeScheme (Base ty) = showType ty
showTypeScheme (Forall name scheme) = "forall " ++ name ++ showTypeScheme' scheme
  where
    showTypeScheme' (Base ty) = ". " ++ showType ty
    showTypeScheme' (Forall name scheme) = " " ++ name ++ showTypeScheme' scheme

showLiteral :: Literal -> String
showLiteral (LitInt a) = show a
showLiteral (LitString a) = show a
showLiteral (LitChar a) = show a
showLiteral (LitBool b) = if b then "true" else "false"

showPattern :: Pattern -> String
showPattern (PatId a) = a
showPattern (PatCon name args) = name ++ unwords args
showPattern (PatLit lit) = showLiteral lit

showValue :: C.Expr -> Maybe String
showValue (Id expr) = Just expr
showValue (Lit lit) = Just $ showLiteral lit
showValue (Abs name expr) = Just "<Function>"
showValue (Error message) = Just $ "Runtime Error: " ++ message
showValue (Prod name args) = unwords . (:) name <$> traverse showValue args
showValue _ = Nothing

repl ::
  ( HasTypeTable s
  , HasContext s
  , HasSymbolTable s
  , HasFreshCount s
  , MonadFree ReplF m
  , Show e
  , AsLexError e
  , AsParseError e
  , AsTypeError e
  , AsInterpreterError e
  , MonadError e m
  , MonadState s m
  )
  => m ()
repl = flip catchError handleError $ do
  input <- readLine
  output <- case input of
    ':':'q':_ -> quit
    ':':'t':rest -> do
      toks <- tokenize rest
      expr <- parseExpression toks
      showTypeScheme <$> typeCheck (S.desugarExpr expr)
    rest -> do
      toks <- tokenize rest
      input <- parseExprOrData toks
      case input of
        ReplExpr expr -> fromJust . showValue <$> evaluate (S.desugarExpr expr)
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
