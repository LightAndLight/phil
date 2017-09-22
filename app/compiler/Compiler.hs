{-# language TemplateHaskell #-}
{-# language OverloadedStrings #-}
import Control.Lens
import Control.Monad.Fresh
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Error.Lens
import Control.Monad.Except
import Data.Monoid
import Options.Applicative
import System.Exit

import qualified Data.Text.IO as T
import qualified Text.Trifecta as Parse

import Phil.AST
import Phil.Core.Codegen
import Phil.Core.Kinds
import Phil.Parser (parseProgram)
import Phil.PHP
import Phil.Sugar
import Phil.Sugar.SyntaxError
import Phil.Typecheck
import Phil.Typecheck.TypeError

data CompilerError
  = CompilerKindError KindError
  | CompilerTypeError TypeError
  | CompilerSyntaxError SyntaxError
  deriving Show

makeClassyPrisms ''CompilerError

instance AsTypeError CompilerError where
  _TypeError = _CompilerTypeError . _TypeError

instance AsKindError CompilerError where
  _KindError = _CompilerKindError . _KindError

instance AsSyntaxError CompilerError where
  _SyntaxError = _CompilerSyntaxError . _SyntaxError

data CompileOpts
  = CompileOpts
  { filepath  :: FilePath
  , useStdout :: Bool
  }

parseCompileOpts :: Parser CompileOpts
parseCompileOpts = CompileOpts <$>
  strArgument
    (metavar "SOURCE" <> help "Source file") <*>
  switch
    (long "stdout" <> help "Print source to stdout")

compile ::
  ( AsTypeError e
  , AsKindError e
  , AsSyntaxError e
  , AsCompilerError e
  , MonadError e m
  , MonadIO m
  )
  => CompileOpts
  -> m ()
compile opts = flip catches handlers $ do
  content <- liftIO . readFile $ filepath opts
  case parseProgram content of
    Parse.Failure err -> liftIO . print $ Parse._errDoc err
    Parse.Success initialAST -> do
      desugaredAST <- traverse desugar initialAST
      typecheckedAST <- runFreshT $ evalStateT (checkDefinitions desugaredAST) initialInferenceState
      let coreAST = fmap toCore typecheckedAST
      let phpAST = genPHP coreAST
      let phpSource = toSource "    " phpAST
      liftIO $ if useStdout opts
        then print phpSource
        else T.writeFile (filepath opts <> ".php") phpSource
  where
    handlers =
      [ handler _TypeError $ liftIO . print . typeErrorMsg
      , handler _KindError $ liftIO . print . kindErrorMsg
      , handler _SyntaxError $ liftIO . print . syntaxErrorMsg
      ]

main :: IO ()
main = do
  opts' <- execParser opts
  res <- runExceptT $ compile opts'
  case (res :: Either CompilerError ()) of
    Right _ -> exitSuccess
    Left err -> die $ show err
  where
    opts = info (helper <*> parseCompileOpts)
      (fullDesc <> progDesc "Compile a Phil source file" <> header "phc - Compiler for the Phil language")
