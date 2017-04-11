{-# language TemplateHaskell #-}

import Control.Lens
import           Control.Monad
import Control.Monad.Fresh
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Error.Lens
import Control.Monad.Except
import Control.Monad.Trans
import Data.Traversable
import           Options.Applicative
import           System.Directory
import           System.Environment
import           System.Exit
import           System.FilePath.Posix
import Text.PrettyPrint hiding ((<>))

import           Lambda.AST
import           Lambda.AST.Definitions (Definition)
import           Lambda.AST.Modules (Module(..))
import           Lambda.Core.Codegen
import           Lambda.Core.Kinds
import           Lambda.Lexer
import           Lambda.Lexer.LexError
import           Lambda.Parser         (parseModule)
import Lambda.Parser.ParseError         hiding (ParseError)
import qualified Lambda.Parser.ParseError         as P (ParseError)
import           Lambda.PHP
import           Lambda.PHP.AST
import           Lambda.Sugar
import           Lambda.Sugar.SyntaxError
import           Lambda.Typecheck
import           Lambda.Typecheck.TypeError

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
  , outputDir :: FilePath
  }

parseCompileOpts :: Parser CompileOpts
parseCompileOpts = CompileOpts <$>
  strArgument
    (metavar "SOURCE" <> help "Source file") <*>
  strOption
    (long "output" <>
    short 'o' <>
    metavar "OUTPUT_DIR" <>
    value "output/" <>
    help "Output directory")

compileModule
  :: ( AsLexError e
     , AsParseError e
     , AsTypeError e
     , AsKindError e
     , AsSyntaxError e
     , AsCompilerError e
     , MonadError e m
     , MonadIO m
     )
  => FilePath
  -> m PHP
compileModule file = do
  content <- liftIO $ readFile file
  tokens <- tokenize content
  moduleAST <- parseModule tokens
  desugaredModule <- traverseOf (traverse.traverse) desugar moduleAST
  typecheckedModule <- for desugaredModule $ \defs -> runFreshT $ evalStateT (checkDefinitions defs) initialInferenceState
  let coreModule = over (mapped.mapped) toCore typecheckedModule
  pure . genPHP $ moduleDefinitions coreModule 

compile
  :: ( AsLexError e
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
  phpAST <- compileModule $ filepath opts
  let phpSource = toSource "    " phpAST
  let destination = outputDir opts </> (takeBaseName (filepath opts) <> ".php")
  liftIO $ do
    createDirectoryIfMissing True $ outputDir opts
    writeFile destination phpSource
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
      (fullDesc <> progDesc "Compile a Lambda source file" <> header "lambdac - Compiler for the Lambda language")
