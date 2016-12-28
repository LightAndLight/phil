{-# language DeriveFunctor #-}
{-# language FlexibleContexts #-}
{-# language Rank2Types #-}

import Control.Lens
import Control.Monad.Except
import Control.Monad.Free
import Control.Monad.Trans
import Control.Monad.State
import Data.Foldable
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

import Lambda
import Lambda.AST (ReplLine(..))
import Lambda.Core
import qualified Lambda.Lexer as L (tokenize)
import Lambda.Lexer hiding (tokenize)
import qualified Lambda.Parser as P (parseExpression, parseExprOrData)
import Lambda.Parser hiding (parseExpression, parseExprOrData)
import Lambda.Translation

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
parseExpression toks = either (throwError . InterpreterParseError) (pure . exprToCore) (P.parseExpression toks)

parseExprOrData :: MonadError InterpreterError m => [Token] -> m ReplLine
parseExprOrData toks = either (throwError . InterpreterParseError) pure (P.parseExprOrData toks)

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
reduce (App func input) = do
  input' <- reduce input
  case func of
    Abs name output -> do
      symbolTable %= M.insert name input'
      reduce output
    PatAbs pat output -> case pat of
      PatCon conName vars -> case input' of
        Prod conName' vals
          | conName == conName' -> do
              for_ (zip vars vals) $ \(var,val) -> symbolTable %= M.insert var val
              reduce output
          | otherwise -> return Fail
        _ -> return Fail
      PatLit lit -> case input' of
        Lit lit'
          | lit == lit' -> reduce output
          | otherwise -> return Fail
        _ -> return Fail
    _ -> App <$> reduce func <*> pure input' >>= reduce
reduce (Abs name expr) = do
  symbolTable %= M.insert name (Id name)
  Abs name <$> reduce expr
reduce (Let name expr rest) = do
  expr' <- reduce expr
  symbolTable %= M.insert name expr'
  reduce rest
reduce (PatAbs pat expr)
  = case pat of
      PatCon conName vars -> do
        defined <- uses symbolTable (M.member conName)
        unless defined . throwError $ NotBound conName
        PatAbs pat <$> reduce expr
      PatLit _ -> PatAbs pat <$> reduce expr
reduce (Chain e1 e2) = do
  e1 <- reduce e1
  case e1 of
    Fail -> reduce e2
    _ -> return e1
reduce (Prod name args) = Prod name <$> traverse reduce args
reduce e = return e

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

declare :: ( HasTypeTable s
           , HasSymbolTable s
           , HasFreshCount s
           , HasContext s
           , MonadFree ReplF m
           , MonadError InterpreterError m
           , MonadState s m
           ) => Definition -> m ()
declare decl = do
  exprs <- liftCompile checkDecl decl
  symbolTable %= M.union exprs

typeCheck :: (HasTypeTable s, HasContext s, HasFreshCount s, MonadFree ReplF m, MonadError InterpreterError m, MonadState s m) => Expr -> m TypeScheme
typeCheck expr = do
  freshCount .= 0
  usingState $ liftCompile w expr

quit :: MonadFree ReplF m => m a
quit = liftF Quit

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
        ReplExpr expr -> fromJust . showValue <$> evaluate (exprToCore expr)
        ReplData name args prods -> declare (Data name args prods) $> ""
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
