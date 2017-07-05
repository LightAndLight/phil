module Phil.AST.Expr where

import Data.List.NonEmpty (NonEmpty)

import Phil.AST.Binding
import Phil.Core.AST.Identifier
import Phil.Core.AST.Literal
import Phil.Core.AST.Pattern
import Phil.Core.AST.Types
import Phil.Typecheck.Unification

type Placeholder = (Identifier, NonEmpty Type)

subPlaceholders subs (DictPlaceholder (className, tyArgs))
  = DictPlaceholder (className, substitute subs <$> tyArgs)
subPlaceholders subs expr = expr

data Expr
  = Id Identifier
  | Lit Literal
  | Prod Identifier [Expr]
  | App Expr Expr
  | Abs Identifier Expr
  | Let (Binding Expr) Expr
  | Rec (Binding Expr) Expr
  | Case Expr (NonEmpty (Pattern, Expr))
  | DictPlaceholder Placeholder
  | RecPlaceholder Identifier
  | DictVar Identifier
  | DictInst Identifier (NonEmpty Identifier)
  | DictSel Identifier Expr
  | DictSuper Identifier Expr
  | Error String
  deriving (Eq, Show)
