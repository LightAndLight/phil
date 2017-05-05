module Lambda.Core.AST.Expr where

import Data.Bifunctor
import           Data.List.NonEmpty         (NonEmpty)
import           Data.Map                   (Map)
import           Data.Set                   (Set)
import           qualified Data.Set                   as S

import           Lambda.Core.AST.Binding
import           Lambda.Core.AST.Identifier
import           Lambda.Core.AST.Literal
import           Lambda.Core.AST.Pattern
import           Lambda.Core.AST.Types

data Expr
  = Id (Maybe (NonEmpty Identifier)) Identifier
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
