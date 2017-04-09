module Lambda.Parser.ParseError where

import Control.Lens
import Text.PrettyPrint

import Lambda.ErrorMsg
import Lambda.Lexer

data ParseError
    = NoMoreTokens
    | Unexpected Token
    deriving Show

class AsParseError e where
  _ParseError :: Prism' e ParseError
  _NoMoreTokens :: Prism' e ()
  _Unexpected :: Prism' e Token

  _NoMoreTokens = _ParseError . _NoMoreTokens
  _Unexpected = _ParseError . _Unexpected

instance AsParseError ParseError where
  _ParseError = prism' id Just
  _NoMoreTokens = prism' (const NoMoreTokens) $ \x -> case x of
    NoMoreTokens -> Just ()
    _ -> Nothing
  _Unexpected = prism' Unexpected $ \x -> case x of
    Unexpected tok -> Just tok
    _ -> Nothing

-- parseErrorMsg :: AsParseError e => e -> Maybe Doc
-- parseErrorMsg = previews _ParseError (errorMsg "Parse error" . toMessage)
parseErrorMsg = errorMsg "Parse error" . toMessage
  where
    toMessage NoMoreTokens
      = text "No more tokens in stream"

    toMessage (Unexpected token)
      = hsep [text "Unexpected token", text $ show token]
