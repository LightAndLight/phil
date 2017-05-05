module Lambda.AST.Expr where

import Data.List.NonEmpty (NonEmpty)

import Lambda.AST.Binding
import Lambda.AST.Modules.ModuleName
import Lambda.Core.AST.Identifier
import Lambda.Core.AST.Literal
import Lambda.Core.AST.Pattern
import Lambda.Core.AST.Types
import Lambda.Typecheck.Unification

type Placeholder = (Identifier, NonEmpty Type)

subPlaceholders subs (DictPlaceholder (className, tyArgs))
  = DictPlaceholder (className, substitute subs <$> tyArgs)
subPlaceholders subs expr = expr

data Expr
  = Id (Maybe ModuleName) Identifier
  | Lit Literal
  | Prod Identifier [Expr]
  | App Expr Expr
  | Abs Identifier Expr
  | Let (Binding Expr) Expr
  | Rec (Binding Expr) Expr
  | Case Expr (NonEmpty (Pattern, Expr))
  | DictPlaceholder Placeholder
  | RecPlaceholder Identifier
  | DictVar (Maybe ModuleName) Identifier
  | DictInst (Maybe ModuleName) Identifier (NonEmpty Identifier)
  | DictSel Identifier Expr
  | DictSuper Identifier Expr
  | Error String
  deriving (Eq, Show)
