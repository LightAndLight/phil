import           Control.Monad
import           Data.Bifunctor
import           System.Environment

import           Lambda.Core.Codegen
import           Lambda.Lexer        (tokenize)
import           Lambda.Parser       (ParseError (..), parseProgram)
import           Lambda.PHP
import           Lambda.Sugar

data CompilerError
  = CompilerParseError ParseError
  | CompilerLexError String
  deriving Show

main :: IO ()
main = do
  file:_ <- getArgs
  content <- readFile file
  let genAst = first CompilerLexError . tokenize
        >=> first CompilerParseError . parseProgram
  let ast = genAst content
  either print (print . toSource "    " . genPHP . fmap desugar) ast
