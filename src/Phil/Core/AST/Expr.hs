module Phil.Core.AST.Expr where

import Data.Text (Text)
import Data.List.NonEmpty (NonEmpty)

import Phil.Core.AST.Binding
import Phil.Core.AST.Identifier
import Phil.Core.AST.Literal
import Phil.Core.AST.Pattern

data Expr
  = Var (Either Ident Ctor)
  | Lit Literal
  | Prod Ctor [Expr]
  | App Expr Expr
  | Abs Ident Expr
  | Let (Binding Expr) Expr
  | Rec (Binding Expr) Expr
  | Case Expr (NonEmpty (Pattern, Expr))
  | Select Expr Text
  | Error String
  deriving (Eq, Show)
