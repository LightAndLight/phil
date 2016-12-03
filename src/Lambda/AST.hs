module Lambda.AST
  ( Definition(..)
  , Pattern(..)
  , Expr(..)
  , Identifier(..)
  , Literal(..)
  , Product(..)
  , ReplLine(..)
  , Type(..)
  ) where

import           Data.List.NonEmpty (NonEmpty (..))

import           Lambda.Core        (Identifier (..), Literal (..),
                                     Product (..), Type (..))

data ReplLine
  = ReplData Identifier [String] (NonEmpty Product)
  | ReplExpr Expr

data Definition
  = Data Identifier [String] (NonEmpty Product)
  | Function Identifier [Pattern] Expr

data Pattern
  = PatCon Identifier [Identifier]
  | PatId Identifier
  | PatLit Literal
  deriving (Eq, Show)

data Expr
  = Id Identifier
  | Lit Literal
  | Prod Identifier [Expr]
  | App Expr Expr
  | Abs Identifier Expr
  | Let Identifier Expr Expr
  | Case Expr (NonEmpty (Pattern,Expr))
  deriving (Eq, Show)
