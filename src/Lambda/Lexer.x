{
module Lambda.Lexer (tokenize) where
}

%wrapper "posn"

$digit = 0-9
$alpha = [a-zA-z]
$upper = [A-Z]
$sym = [\:\!\@\#\$\%\^\&\*\+\-\=\<\>\?\/\|\~]

tokens :-
    $white+;
    "--".*;
    case { \p _ -> WithPos p TokCase }
    of { \p _ -> WithPos p TokOf }
    let { \p _ -> WithPos p TokLet }
    in { \p _ -> WithPos p TokIn }
    forall { \p _ -> WithPos p TokForall }
    "=" { \p _ -> WithPos p TokEq }
    "\\" { \p _ -> WithPos p TokLam }
    "." { \p _ -> WithPos p TokDot }
    ":" { \p _ -> WithPos p TokType }
    "->" { \p _ -> WithPos p TokArr }
    "(" { \p _ -> WithPos p TokLParen }
    ")" { \p _ -> WithPos p TokRParen }
    $upper [$alpha $digit \_ \'] { \p s -> WithPos p $ TokCons s }
    $alpha [$alpha $digit \_ \']* { \p s -> WithPos p $ TokId s }
    $sym+ { \p s -> WithPos p $ TokOp s }
    $digit+ { \p s -> WithPos p $ TokNum s }
   
{
data WithPos = WithPos AlexPosn Token
             | TokEOF
             deriving Show

data Token
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

tokenize str = go (alexStartPos,'\n',[],str)
  where
    go inp@(pos,_,_,str) =
        case alexScan inp 0 of
            AlexEOF -> Right []
            AlexError (pos,_,_,_) -> Left $ LexerError pos
            AlexSkip  inp' len     -> go inp'
            AlexToken inp' len act -> (:) (act pos $ take len str) <$> go inp'

}
