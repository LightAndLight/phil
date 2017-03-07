module Lambda.Core.AST.Expr where

import           Data.List.NonEmpty         (NonEmpty)

import           Lambda.Core.AST.Binding
import           Lambda.Core.AST.Identifier
import           Lambda.Core.AST.Literal
import           Lambda.Core.AST.Pattern

data Expr
  = Id Identifier
  | Lit Literal
  | Prod Identifier [Expr]
  | App Expr Expr
  | Abs Identifier Expr
  | Let (Binding Expr) Expr
  | Rec (Binding Expr) Expr
  | Case Expr (NonEmpty (Pattern,Expr))
  | Error String
  deriving (Eq, Show)
