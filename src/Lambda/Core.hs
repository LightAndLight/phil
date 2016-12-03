module Lambda.Core where

import           Data.List.NonEmpty (NonEmpty)

type Identifier = String

data Product = Product Identifier [Type] deriving (Eq, Show)

data Definition
  = Data Identifier [String] (NonEmpty Product)
  | Binding Identifier Expr
  deriving (Eq, Show)

data Prim
  = Int
  | String
  | Char
  deriving (Eq, Show, Ord)

data Type
  = TypeVar String
  | PrimType Prim
  | FunType Type Type
  | PolyType String [Type]
  deriving (Eq, Show, Ord)

data TypeScheme
  = Base Type
  | Forall String TypeScheme
  deriving (Eq, Show, Ord)

data Literal
  = LitInt Int
  | LitString String
  | LitChar Char
  deriving (Eq, Show)

data Pattern
  = PatCon Identifier [Identifier]
  | PatLit Literal
  deriving (Eq, Show)

data Expr
  = Id Identifier
  | Lit Literal
  | Prod Identifier [Expr]
  | App Expr Expr
  | Abs Identifier Expr
  | Let Identifier Expr Expr
  | PatAbs Pattern Expr
  | Chain Expr Expr
  | Fail
  | Error String
  deriving (Eq, Show)
