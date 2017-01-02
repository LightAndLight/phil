import           Control.Monad
import           Data.Bifunctor
import           Options.Applicative
import           System.Environment

import           Lambda.Core.Codegen
import           Lambda.Core.Typecheck
import           Lambda.Lexer          (tokenize)
import           Lambda.Parser         (parseProgram)
import qualified Lambda.Parser         as P (ParseError)
import           Lambda.PHP
import           Lambda.Sugar

data CompilerError
  = CompilerParseError P.ParseError
  | CompilerLexError String
  | CompilerTypeError TypeError
  deriving Show

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

compile :: CompileOpts -> IO ()
compile opts = do
  content <- readFile $ filepath opts
  let genAst = first CompilerLexError . tokenize
        >=> first CompilerParseError . parseProgram
        >=> first CompilerTypeError . checkDefinitions . fmap desugar
  let ast = genAst content
  case toSource "    " . genPHP <$> ast of
    Left err -> print err
    Right res
      | useStdout opts -> print res
      | otherwise -> writeFile (filepath opts <> ".php") res

main :: IO ()
main = execParser opts >>= compile
  where
    opts = info (helper <*> parseCompileOpts)
      (fullDesc <> progDesc "Compile a Lambda source file" <> header "lambdac - Compiler for the Lambda language")
