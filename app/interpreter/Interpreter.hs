{-# language DeriveFunctor #-}
{-# language FlexibleContexts #-}
{-# language Rank2Types #-}

import Control.Lens
import Control.Monad.Except
import Control.Monad.Free
import Control.Monad.Trans
import Control.Monad.State
import Data.Functor
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
import qualified Lambda.Lexer as L (tokenize)
import Lambda.Lexer hiding (tokenize)
import qualified Lambda.Parser as P (parseExpression, parseExprOrData)
import Lambda.Parser hiding (parseExpression, parseExprOrData)

type SymbolTable = Map Identifier Expr

class HasSymbolTable s where
  symbolTable :: Lens' s (Map Identifier Expr)

data InterpreterState
  = InterpreterState
    { _interpSymbolTable :: Map Identifier Expr
    , _interpTypeTable :: Map Identifier Int
    , _interpContext :: Map Identifier TypeScheme
    , _interpFreshCount :: Int
    }

initialInterpreterState = InterpreterState M.empty M.empty M.empty 0

instance HasSymbolTable InterpreterState where
  symbolTable = lens _interpSymbolTable (\s t -> s { _interpSymbolTable = t })

instance HasContext InterpreterState where
  context = lens _interpContext (\s c -> s { _interpContext = c })

instance HasFreshCount InterpreterState where
  freshCount = lens _interpFreshCount (\s c -> s { _interpFreshCount = c })

instance HasTypeTable InterpreterState where
  typeTable = lens _interpTypeTable (\s t -> s { _interpTypeTable = t })

data InterpreterError
  = NotBound String
  | InterpreterInferenceError InferenceError
  | RuntimeError String
  | InterpreterLexError String
  | InterpreterParseError ParseError
  deriving Show

tokenize :: MonadError InterpreterError m => String -> m [Token]
tokenize rest = either (throwError . InterpreterLexError) pure (L.tokenize rest)

parseExpression :: MonadError InterpreterError m => [Token] -> m Expr
parseExpression toks = either (throwError . InterpreterParseError) pure (P.parseExpression toks)

parseExprOrData :: MonadError InterpreterError m => [Token] -> m ReplInput
parseExprOrData toks = either (throwError . InterpreterParseError) pure (P.parseExprOrData toks)

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
replace name (Prod conName vals) expr = Prod conName $ fmap (flip (replace name) expr) vals
replace name (Error _) _ = error "Error contains no identifier to replace"

tryAll :: MonadError e m => m a -> [m a] -> m a
tryAll e [] = e
tryAll e (e':es) = e `catchError` const (tryAll e' es)

reduce :: (HasSymbolTable s, MonadState s m, MonadError InterpreterError m) => Expr -> m Expr
reduce (Error message) = throwError $ RuntimeError message
reduce (Id name) = do
  maybeExpr <- use (symbolTable . at name)
  case maybeExpr of
    Just expr -> return expr
    Nothing -> throwError $ NotBound name
reduce expr@Lit{} = return expr
reduce (App func input) = case func of
  Abs name output -> do
    input' <- reduce input
    symbolTable %= M.insert name input
    reduce $ replace name output input'
  _ -> App <$> reduce func <*> pure input >>= reduce
reduce (Abs name expr) = do
  symbolTable %= M.insert name (Id name)
  Abs name <$> reduce expr
reduce (Let name expr rest) = do
  expr' <- reduce expr
  symbolTable %= M.insert name expr'
  reduce rest
reduce (Case var []) = error "Malformed AST: Case statement can't have zero branches"
reduce c@(Case var (b:bs)) = do
  var' <- reduce var
  case var' of
    Id{} -> return c
    _ -> tryBranch var' b bs
  where
    inexhaustiveCase = Error "Inexhaustive case expression"
    tryBranch expr (PatId name,b) [] = reduce $ replace name b expr
    tryBranch expr (PatCon con args,b) [] = do
      expr' <- reduce expr
      case expr' of
        Prod name vals
          | con == name -> reduce . foldr (\(a,v) e -> replace a e v) b $ zip args vals
          | otherwise  -> return inexhaustiveCase
        _ -> error "Structure pattern in branch but matching on non-structured value"
    tryBranch expr br@(p,b) [] = do
      expr' <- reduce expr
      return $ case expr' of
        Id a -> b
        Lit a
          | p == PatLit a -> b
          | otherwise -> inexhaustiveCase
        _ -> error "Pattern match on invalid expression"
    tryBranch expr br (b:bs) = do
      res <- tryBranch expr br []
      case res of
        Error _ -> tryBranch expr b bs
        _ -> reduce res
reduce (Prod name args) = Prod name <$> traverse reduce args

liftCompile :: (HasTypeTable s', HasFreshCount s', HasContext s', MonadError InterpreterError m', MonadState s' m')
            => (forall s m. (MonadError InferenceError m, MonadState InferenceState m) => a -> m b)
            -> a -> m' b
liftCompile op a = do
  ctxt <- use context
  fc <- use freshCount
  tt <- use typeTable
  let (res,state) = flip runState (InferenceState ctxt tt fc) . runExceptT $ op a
  case res of
    Left err -> throwError $ InterpreterInferenceError err
    Right res' -> do
      context .= state ^. context
      freshCount .= state ^. freshCount
      typeTable .= state ^. typeTable
      return res'

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

evaluate :: (HasTypeTable s, HasContext s, HasFreshCount s, HasSymbolTable s, MonadFree ReplF m, MonadError InterpreterError m, MonadState s m) => Expr -> m Expr
evaluate expr = do
  usingState (typeCheck expr)
  reduce expr

declare :: (HasTypeTable s, HasSymbolTable s, HasFreshCount s, HasContext s, MonadFree ReplF m, MonadError InterpreterError m, MonadState s m) => Decl -> m ()
declare decl = do
  exprs <- liftCompile checkDecl decl
  symbolTable %= M.union exprs

typeCheck :: (HasTypeTable s, HasContext s, HasFreshCount s, MonadFree ReplF m, MonadError InterpreterError m, MonadState s m) => Expr -> m TypeScheme
typeCheck = usingState . liftCompile w

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

showPattern :: Pattern -> String
showPattern (PatId a) = a
showPattern (PatCon name args) = name ++ unwords args
showPattern (PatLit lit) = showLiteral lit

showValue :: Expr -> Maybe String
showValue (Id expr) = Just expr
showValue (Lit lit) = Just $ showLiteral lit
showValue (Abs name expr) = Just "<Function>"
showValue (Error message) = Just $ "Runtime Error: " ++ message
showValue (Prod name args) = unwords . (:) name <$> traverse showValue args
showValue _ = Nothing

repl :: (HasTypeTable s, HasContext s, HasSymbolTable s, HasFreshCount s, MonadFree ReplF m, MonadError InterpreterError m, MonadState s m) => m ()
repl = flip catchError handleError $ do
  input <- readLine
  output <- case input of
    ':':'q':_ -> quit
    ':':'t':rest -> do
      toks <- tokenize rest
      expr <- parseExpression toks
      showTypeScheme <$> typeCheck expr
    rest -> do
      toks <- tokenize rest
      input <- parseExprOrData toks
      case input of
        ReplExpr expr -> fromJust . showValue <$> evaluate expr
        ReplData dat -> declare (DeclData dat) $> ""
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

main = do
  tempDir <- getTemporaryDirectory
  runInputT defaultSettings
    { historyFile = Just $ tempDir </> "lambdai_history" } $ foldFree replIO (runExceptT . flip evalStateT initialInterpreterState $ repl)
