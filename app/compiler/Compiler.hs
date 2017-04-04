{-# language TemplateHaskell #-}

import Control.Lens
import           Control.Monad
import Control.Monad.Fresh
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Trans
import           Options.Applicative
import           System.Environment

import           Lambda.AST
import           Lambda.Core.Codegen
import           Lambda.Core.Kinds
import           Lambda.Lexer
import           Lambda.Parser         (parseProgram)
import qualified Lambda.Parser         as P (ParseError)
import Lambda.Parser         hiding (ParseError)
import           Lambda.PHP
import           Lambda.Sugar
import           Lambda.Typecheck
import           Lambda.Typecheck.TypeError

data CompilerError
  = CompilerParseError P.ParseError
  | CompilerLexError LexError
  | CompilerTypeError TypeError
  | CompilerSyntaxError SyntaxError
  deriving Show

makeClassyPrisms ''CompilerError

instance AsTypeError CompilerError where
  _TypeError = _CompilerTypeError . _TypeError

instance AsKindError CompilerError where
  _KindError = _CompilerTypeError . _KindError

instance AsParseError CompilerError where
  _ParseError = _CompilerParseError . _ParseError

instance AsLexError CompilerError where
  _LexError = _CompilerLexError . _LexError

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
  ( Show e
  , AsLexError e
  , AsParseError e
  , AsTypeError e
  , AsKindError e
  , AsSyntaxError e
  , AsCompilerError e
  , MonadError e m
  , MonadIO m
  )
  => CompileOpts
  -> m ()
compile opts = flip catchError (liftIO . print) $ do
  content <- liftIO . readFile $ filepath opts
  tokens <- tokenize content
  initialAST <- parseProgram tokens
  desugaredAST <- traverse desugar initialAST
  typecheckedAST <- runFreshT $ evalStateT (checkDefinitions desugaredAST) initialInferenceState
  let coreAST = fmap toCore typecheckedAST
  let phpAST = genPHP coreAST
  let phpSource = toSource "    " phpAST
  liftIO $ if useStdout opts
    then print phpSource
    else writeFile (filepath opts <> ".php") phpSource

main :: IO (Either CompilerError ())
main = execParser opts >>= runExceptT . compile
  where
    opts = info (helper <*> parseCompileOpts)
      (fullDesc <> progDesc "Compile a Lambda source file" <> header "lambdac - Compiler for the Lambda language")
