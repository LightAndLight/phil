module Lambda.Lexer.LexError where

import Control.Lens
import Text.PrettyPrint

import Lambda.ErrorMsg

newtype LexError = MkLexError { getLexError :: String } deriving Show

class AsLexError e where
  _LexError :: Prism' e LexError
  _MkLexError :: Prism' e String

  _MkLexError = _LexError . _MkLexError

instance AsLexError LexError where
  _LexError = prism' id Just
  _MkLexError = prism' MkLexError (Just . getLexError)

-- lexErrorMsg :: AsLexError e => e -> Maybe Doc
-- lexErrorMsg = previews _LexError toMessage
lexErrorMsg = toMessage
  where
    toMessage (MkLexError msg) = errorMsg "Lexical Error" $ text msg
