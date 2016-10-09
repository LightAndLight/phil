{-# language DeriveFunctor #-}
{-# language FlexibleContexts #-}

import Control.Monad.Except
import Control.Monad.Free
import Control.Monad.Trans
import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe
import System.Console.Haskeline
import System.Directory
import System.Exit
import System.FilePath
import System.IO

import Debug.Trace

import Lambda
import Lambda.Lexer
import Lambda.Parser

type SymbolTable = Map Identifier Expr

data InterpreterError
  = NotBound String
  | TypeInferenceError InferenceError
  | RuntimeError String
  deriving Show

replace :: Identifier -> Expr -> Expr -> Expr
replace name (Id name') expr
  | name == name' = expr
  | otherwise = Id name'
replace name expr@Lit{} _ = expr
replace name (Abs name' expr) expr'
  | name == name' = Abs name' expr
  | otherwise = Abs name' (replace name expr expr')
replace name (App f x) expr = App (replace name f expr) (replace name x expr)
replace name (Let name' expr rest) expr'
  | name == name' = Let name' expr rest
  | otherwise = Let name' (replace name expr expr') (replace name rest expr')
replace name (Case var branches) expr
  = Case (replace name var expr) (fmap (replaceBranch name expr) branches)
  where
    replaceBranch :: Identifier -> Expr -> (Pattern,Expr) -> (Pattern,Expr)
    replaceBranch name expr (p@(PatId name'),b)
      | name == name' = (p,b)
      | otherwise = (p,replace name b expr)
    replaceBranch name expr (p@(PatCon conName args),b)
      | name `elem` args = (p,b)
      | otherwise = (p,replace name b expr)
    replaceBranch name expr (p,b) = (p,replace name b expr)
replace name (Error _) _ = error "Error contains no identifier to replace"

tryAll :: MonadError e m => m a -> [m a] -> m a
tryAll e [] = e
tryAll e (e':es) = e `catchError` const (tryAll e' es)

reduce :: (MonadState SymbolTable m, MonadError InterpreterError m) => Expr -> m Expr
reduce (Error message) = throwError $ RuntimeError message
reduce (Id name) = do
  maybeExpr <- gets $ M.lookup name
  case maybeExpr of
    Just expr -> return expr
    Nothing -> throwError $ NotBound name
reduce expr@Lit{} = return expr
reduce (App func input) = case func of
  Abs name output -> do
    input' <- reduce input
    modify $ M.insert name input
    reduce $ replace name output input'
  _ -> App <$> reduce func <*> pure input >>= reduce
reduce (Abs name expr) = do
  modify $ M.insert name (Id name)
  Abs name <$> reduce expr
reduce (Let name expr rest) = do
  reduce expr >>= modify . M.insert name 
  reduce rest
reduce (Case var []) = error "Malformed AST: Case statement can't have zero branches"
reduce c@(Case var (b:bs)) = do
  var' <- reduce var
  case var' of
    Id{} -> return c
    _ -> tryBranch var' b bs
  where
    tryBranch expr (PatId name,b) [] = reduce $ replace name b expr
    tryBranch expr br@(p,b) [] = do
      expr' <- reduce expr
      case expr' of
        Id a -> return b
        Lit a
          | p == PatLit a -> return b
          | otherwise -> return $ Error "Inexhaustive case expression"
        _ -> error "Pattern match on invalid expression"
    tryBranch expr br (b:bs) = do
      res <- tryBranch expr br []
      case res of
        Error _ -> tryBranch expr b bs
        _ -> reduce res

data ReplF a
  = Read (String -> a)
  | Previous (String -> a)
  | TypeCheck Expr a
  | Evaluate Expr a
  | PrintLine String a
  | PrintString String a
  | Quit
  deriving Functor

type Repl a = Free ReplF a

readLine :: Repl String
readLine = liftF $ Read id

printLine :: String -> Repl ()
printLine str = liftF $ PrintLine str ()

printString :: String -> Repl ()
printString str = liftF $ PrintString str ()

evaluate :: Expr -> Repl (Either InterpreterError Expr)
evaluate expr = liftF . Evaluate expr $ evaluate' expr
  where
    evaluate' expr = case w expr of
      Left err -> Left $ TypeInferenceError err
      _        -> runExcept . flip evalStateT M.empty $ reduce expr

typeCheck :: Expr -> Repl (Either InferenceError TypeScheme)
typeCheck expr = liftF . TypeCheck expr $ w expr

quit :: Repl a
quit = liftF Quit

data ParseError = ParseError

parseExpr :: String -> Either ParseError Expr
parseExpr str = Left ParseError

nested :: Type -> String
nested ty@FunType{} = "(" ++ showType ty ++ ")"
nested ty@PolyType{} = "(" ++ showType ty ++ ")"
nested ty = showType ty

showType :: Type -> String
showType (TypeVar name) = name
showType (PrimType ty) = show ty
showType (FunType from to) = nested from ++ " -> " ++ nested to
showType (PolyType cons args) = cons ++ " " ++ unwords (fmap nested args)

showTypeScheme :: TypeScheme -> String
showTypeScheme (Base ty) = showType ty
showTypeScheme (Forall name scheme) = "forall " ++ name ++ showTypeScheme' scheme
  where
    showTypeScheme' (Base ty) = ". " ++ showType ty
    showTypeScheme' scheme = name ++ " " ++ showTypeScheme' scheme

showLiteral :: Literal -> String
showLiteral (LitInt a) = show a
showLiteral (LitString a) = show a
showLiteral (LitChar a) = show a

showPattern :: Pattern -> String
showPattern (PatId a) = a
showPattern (PatCon name args) = name ++ unwords args
showPattern (PatLit lit) = showLiteral lit

showValue :: Expr -> Maybe String
showValue (Id expr) = Just expr
showValue (Lit lit) = Just $ showLiteral lit
showValue (Abs name expr) = Just "<Function>"
showValue (Error message) = Just $ "Runtime Error: " ++ message
showValue a = seq (traceShowId a) Nothing

repl :: Repl ()
repl = do
  input <- readLine
  case input of
    ':':'q':_ -> quit
    ':':'t':rest -> case tokenize rest of
      Right toks -> case parse toks of
        Right expr -> do
          checked <- typeCheck expr
          case checked of
            Right scheme -> printLine $ showTypeScheme scheme
            Left err -> printLine $ show err
        Left err -> printLine $ show err
      Left err -> printLine $ show err
    rest -> case tokenize rest of
      Right toks -> case parse toks of
        Right expr -> do
          evaluated <- evaluate expr
          case evaluated of
            Right expr' -> case showValue expr' of
              Just val -> printLine val
              Nothing -> error "Tree was not reduced to a value"
            Left err -> printLine $ show err
        Left err -> printLine $ show err
      Left err -> printLine $ show err
  repl

replIO :: ReplF a -> InputT IO a
replIO (Read a) = a . fromMaybe "" <$> getInputLine "> "
replIO (TypeCheck _ a) = return a
replIO (Evaluate _ a) = return a
replIO (PrintLine str a) = do
  outputStrLn str
  return a
replIO (PrintString str a) = do
  outputStr str
  -- liftIO $ hFlush stdout
  return a
replIO Quit = liftIO exitSuccess

main = do
  tempDir <- getTemporaryDirectory
  runInputT defaultSettings
    { historyFile = Just $ tempDir </> "lambdai_history" } $ foldFree replIO repl
