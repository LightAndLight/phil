import           Control.Monad
import           Data.Bifunctor
import           System.Environment

import           Lambda.Lexer       (tokenize)
import           Lambda.Parser      (ParseError (..), parseProgram)

data CompilerError
  = CompilerParseError ParseError
  | CompilerLexError String

main = do
  file:_ <- getArgs
  content <- readFile file
  let result = first CompilerParseError . parseProgram
           <=< first CompilerLexError . tokenize $ content
  return result
