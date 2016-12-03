{
module Lambda.Parser (ParseError(..), parseProgram, parseExpression, parseExprOrData) where

import Data.List.NonEmpty (NonEmpty(..), (<|))

import Lambda.AST
import Lambda.Lexer
}

%name parseProgram Start
%name parseExpression SingleExpr
%name parseExprOrData SingleExprOrDataDecl
%monad { Either ParseError }
%tokentype { Token }
%error { parseError }

%token
    eol { Token _ TokEOL }
    data { Token _ TokData }
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
    '"' { Token _ TokDQuote }
    '\'' { Token _ TokSQuote }
    '|' { Token _ TokPipe }

%%

Start : Decls eof { $1 }

Args : ident { [$1] }
     | ident Args { $1:$2 }

PolyType : cons A TypeArgs { PolyType $1 ($2:$3) }

B : A { $1 }
  | A '->' B { FunType $1 $3 }
  | PolyType { $1 }

A : cons { PolyType $1 [] }
  | ident { TypeVar $1 }
  | '(' B ')' { $2 }

TypeArgs : { [] }
         | A TypeArgs { $1:$2 }

Constructor : cons TypeArgs { Product $1 $2 }

Constructors : Constructor { $1 :| [] }
             | Constructor '|' Constructors { $1 <| $3 }

TypeParams : { [] }
           | ident TypeParams { $1:$2 }


SingleExprOrDataDecl : data cons TypeParams '=' Constructors eof { ReplData $2 $3 $5 }
                     | Expr eof { ReplExpr $1 }

Decl : data cons TypeParams '=' Constructors { Data $2 $3 $5 }
     | ident Patterns '=' Expr { Function $1 $2 $4 }

Decls : Decl { [$1] }
      | Decl eol Decls { $1:$3 }

Literal : int { LitInt $ read $1 }
        | '"' string_lit '"' { LitString $2 }
        | '\'' char_lit '\'' { LitChar $ head $2 }

NoArgCon : cons { PatCon $1 [] }

MultiArgCon : cons Args { PatCon $1 $2 }

Pattern : NoArgCon { $1 }
        | MultiArgCon { $1 }
        | Literal { PatLit $1 }

Arg : NoArgCon { $1 }
    | '(' MultiArgCon ')' { $2 }
    | Literal { PatLit $1 }

Patterns : Arg { [$1] }
         | Arg Patterns { $1:$2 }

Branch : Pattern '->' Expr { ($1,$3) }

Branches : Branch eol { $1 :| [] }
         | Branch eol Branches { $1 <| $3 }

Let : let ident '=' Expr in Expr { Let $2 $4 $6 }
Case : case Expr of Branches { Case $2 $4 }
Lam : lam ident '.' Expr { Abs $2 $4 }

ArgExpr : Literal { Lit $1 }
        | ident { Id $1 }
        | cons { Id $1 }
        | '(' Expr ')' { $2 }

FunExpr : ArgExpr { $1 }
        | FunExpr ArgExpr { App $1 $2 }

SingleExpr : Expr eof { $1 }

Expr : FunExpr { $1 }
     | Let { $1 }
     | Lam { $1 }
     | Case { $1 }

{
data ParseError
    = NoMoreTokens
    | Unexpected Token
    deriving Show


parseError [] = Left NoMoreTokens
parseError (t:ts) = Left $ Unexpected t
}
