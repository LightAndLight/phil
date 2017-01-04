{
module Lambda.Lexer (AsLexError(..), LexError(..), Token(..), TokenType(..), tokenize) where

import Control.Lens
import Control.Monad.Except
}

%wrapper "monad"

$digit = 0-9
$alpha = [a-zA-z]
$upper = [A-Z]
$lower = [a-z]
$sym = [\:\!\@\#\$\%\^\&\*\+\-\=\<\>\?\/\|\~]
$eol = [\n\;]

tokens :-
    <0> $eol+ { \(p,_,_,_) _ -> return $ Token p TokEOL }
    <0> $white+;
    <0> "--".*;
    <0> case { \(p,_,_,_) _ -> return $ Token p TokCase }
    <0> data { \(p,_,_,_) _ -> return $ Token p TokData }
    <0> of { \(p,_,_,_) _ -> return $ Token p TokOf }
    <0> let { \(p,_,_,_) _ -> return $ Token p TokLet }
    <0> in { \(p,_,_,_) _ -> return $ Token p TokIn }
    <0> forall { \(p,_,_,_) _ -> return $ Token p TokForall }
    <0> true { \(p,_,_,_) _ -> return $ Token p TokTrue }
    <0> false { \(p,_,_,_) _ -> return $ Token p TokFalse }
    <0> Int { \(p,_,_,_) _ -> return $ Token p TokIntType }
    <0> String { \(p,_,_,_) _ -> return $ Token p TokStringType }
    <0> Char { \(p,_,_,_) _ -> return $ Token p TokCharType }
    <0> Bool { \(p,_,_,_) _ -> return $ Token p TokBoolType }
    <0> "=" { \(p,_,_,_) _ -> return $ Token p TokEq }
    <0> "_" { \(p,_,_,_) _ -> return $ Token p TokWildcard }
    <0> \\ { \(p,_,_,_) _ -> return $ Token p TokLam }
    <0> "." { \(p,_,_,_) _ -> return $ Token p TokDot }
    <0> "|" { \(p,_,_,_) _ -> return $ Token p TokPipe }
    <0> ":" { \(p,_,_,_) _ -> return $ Token p TokType }
    <0> "->" { \(p,_,_,_) _ -> return $ Token p TokArr }
    <0> "(" { \(p,_,_,_) _ -> return $ Token p TokLParen }
    <0> ")" { \(p,_,_,_) _ -> return $ Token p TokRParen }
    <0> "{" { \(p,_,_,_) _ -> return $ Token p TokLBrace }
    <0> "}" { \(p,_,_,_) _ -> return $ Token p TokRBrace }
    <0> \" { beginString }
    <stringSC> (\\.|[^\"])* { \(p,_,_,s) n -> return $ Token p $ TokString (take n s) }
    <stringSC> \" { endString }
    <0> "'" { beginChar }
    <charSC> (\\.|[^\']) { \(p,_,_,s) n -> return $ Token p $ TokChar (take n s) }
    <charSC> "'" { endChar }
    <0> $upper [$alpha $digit \_ \']* { \(p,_,_,s) n -> return $ Token p $ TokCons (take n s) }
    <0> $lower [$alpha $digit \_ \']* { \(p,_,_,s) n -> return $ Token p $ TokId (take n s) }
    <0> $sym+ { \(p,_,_,s) n -> return $ Token p $ TokOp (take n s) }
    <0> $digit+ { \(p,_,_,s) n -> return $ Token p $ TokNum (take n s) }

{

beginString (p,_,_,_) _ = alexSetStartCode stringSC >> return (Token p $ TokDQuote)
endString (p,_,_,_) _ = alexSetStartCode 0 >> return (Token p $ TokDQuote)

beginChar (p,_,_,_) _ = alexSetStartCode charSC >> return (Token p $ TokSQuote)
endChar (p,_,_,_) _ = alexSetStartCode 0 >> return (Token p $ TokSQuote)

data Token = Token AlexPosn TokenType
             | TokEOF
             deriving Show

data TokenType
    = TokCase
    | TokOf
    | TokData
    | TokLet
    | TokIn
    | TokPipe
    | TokEq
    | TokLam
    | TokForall
    | TokDot
    | TokArr
    | TokType
    | TokEOL
    | TokLParen
    | TokRParen
    | TokLBrace
    | TokRBrace
    | TokCons String
    | TokId String
    | TokOp String
    | TokNum String
    | TokDQuote
    | TokSQuote
    | TokString String
    | TokChar String
    | TokTrue
    | TokFalse
    | TokWildcard
    | TokIntType
    | TokStringType
    | TokCharType
    | TokBoolType
    deriving Show

newtype LexError = MkLexError { getLexError :: String } deriving Show

class AsLexError e where
  _LexError :: Prism' e LexError
  _MkLexError :: Prism' e String

  _MkLexError = _LexError . _MkLexError

instance AsLexError LexError where
  _LexError = prism' id Just
  _MkLexError = prism' MkLexError (Just . getLexError)

alexEOF = return TokEOF

tokenize :: (AsLexError e, MonadError e m) => String -> m [Token]
tokenize str = either (throwError . review _MkLexError) pure $ runAlex str loop
  where
    loop = do
        res <- alexMonadScan
        case res of
            TokEOF -> return [res]
            _ -> (:) res <$> loop

}
