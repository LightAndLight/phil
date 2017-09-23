module Phil.AST.Expr where

import Data.List.NonEmpty (NonEmpty)

import Phil.AST.Binding
import Phil.Core.AST.Identifier
import Phil.Core.AST.Literal
import Phil.Core.AST.Pattern
import Phil.Core.AST.Types
import Phil.Typecheck.Unification

type Placeholder = (Ctor, NonEmpty Type)

subPlaceholders subs (DictPlaceholder (className, tyArgs))
  = DictPlaceholder (className, substitute subs <$> tyArgs)
subPlaceholders _ expr = expr

data Expr
  = Var (Either Ident Ctor)
  | Lit Literal
  | Prod Ctor [Expr]
  | App Expr Expr
  | Abs Ident Expr
  | Let (Binding Expr) Expr
  | Rec (Binding Expr) Expr
  | Case Expr (NonEmpty (Pattern, Expr))
  | DictPlaceholder Placeholder
  | RecPlaceholder Ident
  | DictVar Ident
  | DictInst Ctor (NonEmpty Ctor)
  | DictSel Ident Expr
  | DictSuper Ctor Expr
  | Error String
  deriving (Eq, Show)
