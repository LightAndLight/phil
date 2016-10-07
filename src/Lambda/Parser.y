{
module Lambda.Parser (parse) where

import Lambda
import Lambda.Lexer
}

%name parse
%monad { Either ParseError }
%tokentype { Token }
%error { parseError }

%token
    case { Token _ TokCase }
    of { Token _ TokOf }
    let { Token _ TokLet }
    in { Token _ TokIn }
    forall { Token _ TokForall }
    cons { Token _ (TokCons $$) }
    ident { Token _ (TokId $$) }
    op { Token _ (TokOp $$) }
    int { Token _ (TokNum $$) }
    string_lit { Token _ (TokString $$) }
    char_lit { Token _ (TokChar $$) }
    eof { TokEOF }
    lam { Token _ TokLam }
    '=' { Token _ TokEq }
    '.' { Token _ TokDot }
    '->' { Token _ TokArr }
    ':' { Token _ TokType }
    '(' { Token _ TokLParen }
    ')' { Token _ TokRParen }
    ';' { Token _ TokSep }
    '"' { Token _ TokDQuote }
    '\'' { Token _ TokSQuote }

%%

Start : Expr eof { $1 }

Expr : '(' Expr ')' { $2 }
     | ident { Id $1 }
     | Literal { Lit $1 }
     | lam ident '.' Expr { Abs $2 $4 }
     | let ident '=' Expr in Expr { Let $2 $4 $6 }
     | case Expr of Branches { Case $2 $4 }
     | Expr Expr { App $1 $2 }

Literal : int { LitInt $ read $1 }
        | '"' string_lit '"' { LitString $2 }
        | '\'' char_lit '\'' { LitChar $ head $2 }

Branches : Branch { [$1] }
         | Branch ';' Branches { $1:$3 }

Branch : Pattern '->' Expr { ($1,$3) }

Pattern : cons Args { PatCon $1 $2 }
        | ident { PatId $1 }
        | Literal { PatLit $1 }

Args : { [] }
     | ident Args { $1:$2 }

{
data ParseError
    = NoMoreTokens
    | Unexpected Token


parseError [] = Left NoMoreTokens
parseError (t:ts) = Left $ Unexpected t
}
