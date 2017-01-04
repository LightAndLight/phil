{
{-# language TemplateHaskell #-}

module Lambda.Parser
  ( AsParseError(..)
  , ParseError(..)
  , ReplInput(..)
  , parseProgram
  , parseExpression
  , parseExprOrData
  )
  where

import Control.Lens (Prism', prism', review)
import Control.Monad.Except
import Data.List.NonEmpty (NonEmpty(..), (<|))

import Lambda.Lexer
import Lambda.Core.AST hiding (Expr(..), Definition(..))
import Lambda.Sugar

}

%name parseProgramI Start
%name parseExpressionI SingleExpr
%name parseExprOrDataI ExprOrDef
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
    true { Token _ TokTrue }
    false { Token _ TokFalse }
    cons { Token _ (TokCons $$) }
    ident { Token _ (TokId $$) }
    op { Token _ (TokOp $$) }
    int { Token _ (TokNum $$) }
    string_lit { Token _ (TokString $$) }
    char_lit { Token _ (TokChar $$) }
    eof { TokEOF }
    lam { Token _ TokLam }
    intType { Token _ TokIntType }
    stringType { Token _ TokStringType }
    charType { Token _ TokCharType }
    boolType { Token _ TokBoolType }
    '=' { Token _ TokEq }
    '_' { Token _ TokWildcard }
    '.' { Token _ TokDot }
    '->' { Token _ TokArr }
    ':' { Token _ TokType }
    '(' { Token _ TokLParen }
    ')' { Token _ TokRParen }
    '{' { Token _ TokLBrace }
    '}' { Token _ TokRBrace }
    '"' { Token _ TokDQuote }
    '\'' { Token _ TokSQuote }
    '|' { Token _ TokPipe }

%%

Start : Definitions eof { $1 }

Args : ident { [$1] }
     | ident Args { $1:$2 }

Ty : B { $1 }
   | B '->' Ty { FunType $1 $3 }

B : cons TypeArgs { PolyType $1 $2 }
  | A { $1 }

A : ident { TypeVar $1 }
  | PrimType { PrimType $1 }
  | '(' Ty ')' { $2 }

PrimType : intType { Int }
         | stringType { String }
         | charType { Char }
         | boolType { Bool }


TypeArgs : { [] }
         | A TypeArgs { $1:$2 }

Constructor : cons TypeArgs { ProdDecl $1 $2 }

Constructors : Constructor { $1 :| [] }
             | Constructor '|' Constructors { $1 <| $3 }

DataDefinition : data cons Args '=' Constructors { Data $2 $3 $5 }
               | data cons '=' Constructors { Data $2 [] $4 }

QuantifiedType : Ty { Base $1 }
               | forall Args '.' Ty { foldr Forall (Base $4) $2 }

TypeSignature : ident ':' QuantifiedType { TypeSignature $1 $3 }

FunctionDefinition : ident FunctionArgs '=' Expr { FunctionDefinition $1 $2 $4 }

ExprOrDef : DataDefinition eof { ReplDef $1 }
          | Expr eof { ReplExpr $1 }

FunctionArgs : { [] }
             | ident FunctionArgs { $1:$2 }

Definition : DataDefinition { $1 }
           | FunctionDefinition { Function $1 }
           | TypeSignature { $1 }

Definitions : { [] }
            | Definition eol Definitions { $1:$3 }

Literal : int { LitInt $ read $1 }
        | '"' string_lit '"' { LitString $2 }
        | '\'' char_lit '\'' { LitChar $ head $2 }
        | true { LitBool True }
        | false { LitBool False }

NoArgCon : cons { PatCon $1 [] }

MultiArgCon : cons Args { PatCon $1 $2 }

Pattern : NoArgCon { $1 }
        | MultiArgCon { $1 }
        | ident { PatId $1 }
        | Literal { PatLit $1 }
        | '_' { PatWildcard }

Arg : NoArgCon { $1 }
    | '(' MultiArgCon ')' { $2 }
    | ident { PatId $1 }
    | Literal { PatLit $1 }

Patterns : Arg { [$1] }
         | Arg Patterns { $1:$2 }

Branch : Pattern '->' Expr { ($1,$3) }

Branches : Branch { $1 :| [] }
         | Branch eol Branches { $1 <| $3 }

Let : let FunctionDefinition in Expr { Let $2 $4 }
Case : case Expr of '{' Branches '}' { Case $2 $5 }
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

data ReplInput
  = ReplDef Definition
  | ReplExpr Expr

parseError [] = Left NoMoreTokens
parseError (t:ts) = Left $ Unexpected t

parseExpression :: (AsParseError e, MonadError e m) => [Token] -> m Expr
parseExpression = either (throwError . review _ParseError) pure . parseExpressionI

parseExprOrData :: (AsParseError e, MonadError e m) => [Token] -> m ReplInput
parseExprOrData = either (throwError . review _ParseError) pure . parseExprOrDataI

parseProgram :: (AsParseError e, MonadError e m) => [Token] -> m [Definition]
parseProgram = either (throwError . review _ParseError) pure . parseProgramI
}
