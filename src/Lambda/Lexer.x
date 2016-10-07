{
module Lambda.Lexer (tokenize) where
}

%wrapper "monad"

$digit = 0-9
$alpha = [a-zA-z]
$upper = [A-Z]
$sym = [\:\!\@\#\$\%\^\&\*\+\-\=\<\>\?\/\|\~]

tokens :-
    $white+;
    "--".*;
    case { \(p,_,_,_) _ -> return $ Token p TokCase }
    of { \(p,_,_,_) _ -> return $ Token p TokOf }
    let { \(p,_,_,_) _ -> return $ Token p TokLet }
    in { \(p,_,_,_) _ -> return $ Token p TokIn }
    forall { \(p,_,_,_) _ -> return $ Token p TokForall }
    "=" { \(p,_,_,_) _ -> return $ Token p TokEq }
    "\\" { \(p,_,_,_) _ -> return $ Token p TokLam }
    "." { \(p,_,_,_) _ -> return $ Token p TokDot }
    ":" { \(p,_,_,_) _ -> return $ Token p TokType }
    "->" { \(p,_,_,_) _ -> return $ Token p TokArr }
    "(" { \(p,_,_,_) _ -> return $ Token p TokLParen }
    ")" { \(p,_,_,_) _ -> return $ Token p TokRParen }
    $upper [$alpha $digit \_ \'] { \(p,_,_,s) n -> return $ Token p $ TokCons (take n s) }
    $alpha [$alpha $digit \_ \']* { \(p,_,_,s) n -> return $ Token p $ TokId (take n s) }
    $sym+ { \(p,_,_,s) n -> return $ Token p $ TokOp (take n s) }
    $digit+ { \(p,_,_,s) n -> return $ Token p $ TokNum (take n s) }
   
{
data Token = Token AlexPosn TokenType
             | TokEOF
             deriving Show

data TokenType
    = TokCase
    | TokOf
    | TokLet
    | TokIn
    | TokEq
    | TokLam
    | TokForall
    | TokDot
    | TokArr
    | TokType
    | TokLParen
    | TokRParen
    | TokCons String
    | TokId String
    | TokOp String
    | TokNum String
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
