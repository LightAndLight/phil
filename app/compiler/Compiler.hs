{-# language TemplateHaskell #-}

import Control.Lens
import Control.Monad
import Control.Monad.Fresh
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Error.Lens
import Control.Monad.Except
import Control.Monad.Trans
import Data.Monoid
import Options.Applicative
import System.Environment
import System.Exit
import Text.PrettyPrint hiding ((<>))

import Phil.AST
import Phil.Core.Codegen
import Phil.Core.Kinds
import Phil.Lexer
import Phil.Lexer.LexError
import Phil.Parser         (parseProgram)
import Phil.Parser.ParseError         hiding (ParseError)
import Phil.PHP
import Phil.Sugar
import Phil.Sugar.SyntaxError
import Phil.Typecheck
import Phil.Typecheck.TypeError
import qualified Phil.Parser.ParseError         as P (ParseError)

data CompilerError
  = CompilerParseError P.ParseError
  | CompilerLexError LexError
  | CompilerKindError KindError
  | CompilerTypeError TypeError
  | CompilerSyntaxError SyntaxError
  deriving Show

makeClassyPrisms ''CompilerError

instance AsTypeError CompilerError where
  _TypeError = _CompilerTypeError . _TypeError

instance AsKindError CompilerError where
  _KindError = _CompilerKindError . _KindError

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
  ( AsLexError e
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
compile opts = flip catches handlers $ do
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
  where
    handlers =
      [ handler _LexError $ liftIO . putStrLn . render . lexErrorMsg
      , handler _ParseError $ liftIO . putStrLn . render . parseErrorMsg
      , handler _TypeError $ liftIO . putStrLn . render . typeErrorMsg
      , handler _KindError $ liftIO . putStrLn . render . kindErrorMsg
      , handler _SyntaxError $ liftIO . putStrLn . render . syntaxErrorMsg
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
