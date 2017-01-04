module Lambda.Core.AST where

import           Data.List.NonEmpty (NonEmpty)

data Prim
  = Int
  | String
  | Char
  | Bool
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

type Identifier = String

data Literal = LitInt Int
             | LitString String
             | LitChar Char
             | LitBool Bool
             deriving (Eq, Show)

data Pattern = PatId Identifier
             | PatCon Identifier [Identifier]
             | PatLit Literal
             deriving (Eq, Show)

data ProdDecl = ProdDecl Identifier [Type]

data Definition
  = Data Identifier [Identifier] (NonEmpty ProdDecl)
  | Binding Identifier Expr

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
