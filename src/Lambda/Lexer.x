{
module Lambda.Lexer (Token(..), TokenType(..), tokenize) where
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
    <0> "=" { \(p,_,_,_) _ -> return $ Token p TokEq }
    <0> \\ { \(p,_,_,_) _ -> return $ Token p TokLam }
    <0> "." { \(p,_,_,_) _ -> return $ Token p TokDot }
    <0> "|" { \(p,_,_,_) _ -> return $ Token p TokPipe }
    <0> ":" { \(p,_,_,_) _ -> return $ Token p TokType }
    <0> "->" { \(p,_,_,_) _ -> return $ Token p TokArr }
    <0> "(" { \(p,_,_,_) _ -> return $ Token p TokLParen }
    <0> ")" { \(p,_,_,_) _ -> return $ Token p TokRParen }
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
    | TokCons String
    | TokId String
    | TokOp String
    | TokNum String
    | TokDQuote
    | TokSQuote
    | TokString String
    | TokChar String
    deriving Show

data LexerError = LexerError AlexPosn deriving Show

alexEOF = return TokEOF

tokenize str = runAlex str loop
  where
    loop = do
        res <- alexMonadScan
        case res of
            TokEOF -> return [res]
            _ -> (:) res <$> loop

}
