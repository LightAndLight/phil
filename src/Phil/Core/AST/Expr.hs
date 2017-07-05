module Phil.Core.AST.Expr where

import Data.Bifunctor
import           Data.List.NonEmpty         (NonEmpty)
import           Data.Map                   (Map)
import           Data.Set                   (Set)
import           qualified Data.Set                   as S

import           Phil.Core.AST.Binding
import           Phil.Core.AST.Identifier
import           Phil.Core.AST.Literal
import           Phil.Core.AST.Pattern
import           Phil.Core.AST.Types

data Expr
  = Id Identifier
  | Lit Literal
  | Prod Identifier [Expr]
  | App Expr Expr
  | Abs Identifier Expr
  | Let (Binding Expr) Expr
  | Rec (Binding Expr) Expr
  | Case Expr (NonEmpty (Pattern, Expr))
  | Select Expr Identifier
  | Error String
  deriving (Eq, Show)
