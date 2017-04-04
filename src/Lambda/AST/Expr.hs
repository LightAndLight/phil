module Lambda.AST.Expr where

import Data.List.NonEmpty (NonEmpty)

import Lambda.AST.Binding
import Lambda.Core.AST.Identifier
import Lambda.Core.AST.Literal
import Lambda.Core.AST.Pattern
import Lambda.Core.AST.Types

data Expr
  = Id Identifier
  | Lit Literal
  | Prod Identifier [Expr]
  | App Expr Expr
  | Abs Identifier Expr
  | Let (Binding Expr) Expr
  | Rec (Binding Expr) Expr
  | Case Expr (NonEmpty (Pattern, Expr))
  | DictPlaceholder (Identifier, NonEmpty Type)
  | RecPlaceholder Identifier
  | DictVar Identifier
  | DictInst Identifier (NonEmpty Identifier)
  | DictSel Identifier Expr
  | DictSuper Identifier Expr
  | Error String
  deriving (Eq, Show)
