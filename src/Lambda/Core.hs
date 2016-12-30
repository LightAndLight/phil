module Lambda.Core where

import           Data.List.NonEmpty

type Identifier = String

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
  = PatId Identifier
  | PatCon Identifier [Identifier]
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
  | Error String
  deriving (Eq, Show)

data ProdDecl = ProdDecl Identifier [Type]
data Declaration
  = Data Identifier [Identifier] (NonEmpty ProdDecl)
  | Binding Identifier Expr
