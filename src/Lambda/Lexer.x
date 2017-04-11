{
module Lambda.Lexer (Token(..), TokenType(..), tokenize) where

import Control.Lens
import Control.Monad.Except

import Lambda.Lexer.LexError
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
    <0> class { \(p,_,_,_) _ -> return $ Token p TokClass }
    <0> instance { \(p,_,_,_) _ -> return $ Token p TokInstance }
    <0> where { \(p,_,_,_) _ -> return $ Token p TokWhere }
    <0> import { \(p,_,_,_) _ -> return $ Token p TokImport }
    <0> module { \(p,_,_,_) _ -> return $ Token p TokModule }
    <0> case { \(p,_,_,_) _ -> return $ Token p TokCase }
    <0> data { \(p,_,_,_) _ -> return $ Token p TokData }
    <0> of { \(p,_,_,_) _ -> return $ Token p TokOf }
    <0> let { \(p,_,_,_) _ -> return $ Token p TokLet }
    <0> rec { \(p,_,_,_) _ -> return $ Token p TokRec }
    <0> in { \(p,_,_,_) _ -> return $ Token p TokIn }
    <0> forall { \(p,_,_,_) _ -> return $ Token p TokForall }
    <0> true { \(p,_,_,_) _ -> return $ Token p TokTrue }
    <0> false { \(p,_,_,_) _ -> return $ Token p TokFalse }
    <0> "=" { \(p,_,_,_) _ -> return $ Token p TokEq }
    <0> "_" { \(p,_,_,_) _ -> return $ Token p TokWildcard }
    <0> \\ { \(p,_,_,_) _ -> return $ Token p TokLam }
    <0> "." { \(p,_,_,_) _ -> return $ Token p TokDot }
    <0> "," { \(p,_,_,_) _ -> return $ Token p TokComma }
    <0> "|" { \(p,_,_,_) _ -> return $ Token p TokPipe }
    <0> ":" { \(p,_,_,_) _ -> return $ Token p TokType }
    <0> "->" { \(p,_,_,_) _ -> return $ Token p TokArr }
    <0> "=>" { \(p,_,_,_) _ -> return $ Token p TokConstraint }
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
    | TokClass
    | TokInstance
    | TokWhere
    | TokOf
    | TokData
    | TokLet
    | TokRec
    | TokIn
    | TokPipe
    | TokEq
    | TokLam
    | TokForall
    | TokDot
    | TokComma
    | TokArr
    | TokConstraint
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
    | TokImport
    | TokModule
    deriving Show

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
