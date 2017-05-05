{-# language TemplateHaskell #-}
{-# language FlexibleContexts #-}

import Control.Lens hiding ((<.>))
import           Control.Monad
import Control.Monad.Fresh
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Error.Lens
import Control.Monad.Except
import Control.Monad.Trans
import Data.Foldable
import Data.List.NonEmpty
import Data.Traversable
import           Options.Applicative
import           System.Directory
import           System.Environment
import           System.Exit
import           System.FilePath.Posix
import Text.PrettyPrint hiding ((<>))

import qualified Data.List.NonEmpty as N

import           Lambda.AST
import           Lambda.AST.Definitions (Definition)
import           Lambda.AST.Modules
import           Lambda.Core.AST.Identifier
import           Lambda.Core.Codegen
import           Lambda.Core.Kinds
import           Lambda.Lexer
import           Lambda.Lexer.LexError
import           Lambda.Parser         (parseModule)
import Lambda.Parser.ParseError         hiding (ParseError)
import           Lambda.PHP
import           Lambda.PHP.AST
import           Lambda.PHP.Import
import           Lambda.Sugar
import           Lambda.Sugar.SyntaxError
import           Lambda.Typecheck
import           Lambda.Typecheck.Module
import           Lambda.Typecheck.TypeError

import qualified Lambda.Parser.ParseError         as P (ParseError)

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

-- | Compile a desugared, typechecked module
compileModule
  :: ( AsLexError e
     , AsParseError e
     , AsTypeError e
     , AsKindError e
     , AsSyntaxError e
     , AsCompilerError e
     , MonadError e m
     )
  => Module [Definition]
  -> m (Module PHP)
compileModule typecheckedModule = do
  let coreModule = over (mapped.mapped) toCore typecheckedModule
  pure (coreModule & moduleData .~ genPHP coreModule)

modulePath :: NonEmpty Identifier -> FilePath
modulePath = foldr1 (</>)

compileDependencies
  :: ( AsLexError e
     , AsParseError e
     , AsTypeError e
     , AsKindError e
     , AsSyntaxError e
     , AsCompilerError e
     , MonadError e m
     , MonadIO m
     )
  => FilePath -- ^ Absolute path of output directory
  -> FilePath -- ^ Absolute path to working directory
  -> NonEmpty Identifier -- ^ Primary module name
  -> m (Module PHP)
compileDependencies outputDir workingDir mainModuleName = do
  (mainModule : dependencies) <-
    flip evalStateT initialInferenceState .
    runFreshT $ go [] mainModuleName
  traverse_ (writeModule outputDir) dependencies
  pure mainModule
  where
    go parents currentModule = do
      moduleAST <- checkModule workingDir currentModule

      let modName = moduleAST ^. moduleName
      when (modName `elem` parents) .
        throwError $ _ModuleCycle # (modName : parents)

      case moduleAST ^. moduleImports of
        [] -> pure <$> compileModule moduleAST
        childs -> do
          dependencies <- foldrM
            (\child rest -> do
                new <- go (modName : parents) child
                pure $ new <> rest
            )
            []
            childs
          compiled <- compileModule moduleAST
          pure $ compiled : dependencies

-- | Entry point to compiling the module graph
-- 
-- Compiles file & dependencies then inserts bootstrapping components
compileMainModule
  :: ( AsLexError e
     , AsParseError e
     , AsTypeError e , AsKindError e
     , AsSyntaxError e
     , AsCompilerError e
     , MonadError e m
     , MonadIO m
     )
  => FilePath -- ^ Absolute path of output directory
  -> FilePath -- ^ Absolute path of the file containing the module
  -> m ()
compileMainModule outputDir mainPath = do
  liftIO $ createDirectoryIfMissing True outputDir
  mainModule <- compileDependencies
    outputDir
    (takeDirectory mainPath)
    (pure $ takeBaseName mainPath)
  bootstrapImport $ outputDir </> "import.php"
  let includeImport
        = PHPDeclStatement .
          PHPStatementInclude .
          PHPExprLiteral $
          PHPString "import.php"
  let mainModule' = fmap (consPHPDecl includeImport) mainModule
  liftIO $ writeModule outputDir mainModule'

-- | Write a PHP module to a file in a specific directory. Assumes the
-- directory exists.
writeModule
  :: MonadIO m
  => FilePath -- ^ Output directory
  -> Module PHP
  -> m ()
writeModule outputDir phpModule = do
  let path = (outputDir </> modulePath (phpModule ^. moduleName)) <.> "php"
  liftIO . createDirectoryIfMissing True $ takeDirectory path
  let moduleSource = toSource "    " (phpModule ^. moduleData)
  liftIO $ writeFile path moduleSource

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
  let path = filepath opts
  compileMainModule (outputDir opts) (filepath opts)
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
