{-# language DeriveFunctor #-}
{-# language FlexibleContexts #-}

module Lambda.Interpreter where

import Control.Monad.Except
import Control.Monad.Free
import Control.Monad.State
import Data.List.NonEmpty
import Data.Map (Map)
import qualified Data.Map as M

import Lambda

type SymbolTable = Map Identifier Expr

data InterpreterError
  = NotBound String
  | TypeInferenceError InferenceError
  | InexhaustivePattern (Pattern,Expr)
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

tryAll :: MonadError e m => m a -> [m a] -> m a
tryAll e [] = e
tryAll e (e':es) = e `catchError` const (tryAll e' es)

reduce :: (MonadState SymbolTable m, MonadError InterpreterError m) => Expr -> m Expr
reduce (Id name) = do
  maybeExpr <- gets $ M.lookup name
  case maybeExpr of
    Just expr -> return expr
    Nothing -> throwError $ NotBound name
reduce expr@Lit{} = return expr
reduce (App func input) = do
  func' <- reduce func
  case func' of
    Abs name output -> replace name <$> reduce output <*> reduce input
    _ -> error "Malformed AST: App node without Abs on left hand side"
reduce (Abs name expr) = Abs name <$> reduce expr
reduce (Let name expr rest) = do
  reduce expr >>= modify . M.insert name
  reduce rest
reduce (Case var []) = error "Malformed AST: Case statement can't have zero branches"
reduce (Case var (b:bs)) = do
  var' <- reduce var
  tryAll (tryBranch var' b) (fmap (tryBranch var') bs)
  where
    tryBranch (Id a) _ = error "Reduction Error: Identifier was not replaced"
    tryBranch (App a1 a2) _ = error "Reduction Error: Application was not reduced"
    tryBranch (Abs a1 a2) _ = error "Malformed AST: Pattern matching on function"
    tryBranch (Let a1 a2 a3) _ = error "Reduction Error: Let was not reduced"
    tryBranch (Case a1 a2) _ = error "Reduction Error: Case was not reduced"
    tryBranch (Lit a) (PatId name,b) = return $ replace name b (Lit a)
    tryBranch _ (PatCon p1 p2,b) = error "Malformed AST: Literal matches as constructor"
    tryBranch (Lit a) br@(PatLit a',b)
      | a == a' = return b
      | otherwise = throwError $ InexhaustivePattern br

--typeCheck :: Expr -> Either InferenceError TypeScheme
--typeCheck expr = w expr M.empty

data ReplF a
  = Read (String -> a)
  | TypeCheck Expr a
  | Evaluate Expr a
  | Print String a
  | Quit a
  deriving Functor

type Repl a = Free ReplF a

readLine :: Repl String
readLine = liftF $ Read id

printLine :: String -> Repl ()
printLine str = liftF $ Print str ()

evaluate :: Expr -> Repl (Either InterpreterError Expr)
evaluate expr = liftF . Evaluate expr $ evaluate' expr
  where
    evaluate' expr = case w expr M.empty of
      Left err -> Left $ TypeInferenceError err
      _        -> runExcept . flip evalStateT M.empty $ reduce expr

typeCheck :: Expr -> Repl (Either InferenceError TypeScheme)
typeCheck expr = liftF . TypeCheck expr $ w expr M.empty

quit :: Repl ()
quit = liftF $ Quit ()

data ParseError = ParseError

parseExpr :: String -> Either ParseError Expr
parseExpr str = Left ParseError

showTypeScheme :: TypeScheme -> String
showTypeScheme scheme = ""

showError :: ParseError -> String
showError err = ""

showInferenceError :: InferenceError -> String
showInferenceError err = ""

showInterpreterError :: InterpreterError -> String
showInterpreterError err = ""

showExpr :: Expr -> String
showExpr expr = ""

repl :: Repl ()
repl = do
  input <- readLine
  case input of
    ":q" -> quit
    ':':'t':rest -> case parseExpr rest of
      Right expr -> do
        checked <- typeCheck expr
        case checked of
          Right scheme -> printLine $ showTypeScheme scheme
          Left err -> printLine $ showInferenceError err
      Left err -> printLine $ showError err
    rest -> case parseExpr rest of
      Right expr -> do
        evaluated <- evaluate expr
        case evaluated of
          Right expr' -> printLine $ showExpr expr'
          Left err -> printLine $ showInterpreterError err
      Left err -> printLine $ showError err
  repl

