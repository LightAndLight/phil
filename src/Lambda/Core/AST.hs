module Lambda.Core.AST where

import           Data.List.NonEmpty (NonEmpty)

data Prim
  = Int
  | String
  | Char
  | Bool
  deriving (Eq, Show, Ord)

data TyCon = FunTy | DataTy Identifier deriving (Eq, Show, Ord)

data Type
  = TyVar String
  | TyApp Type Type
  | TyCon TyCon
  | TyPrim Prim
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
             | PatWildcard
             deriving (Eq, Show)

data ProdDecl = ProdDecl Identifier [Type]

data Binding
  = Binding
  { bindingName  :: Identifier
  , bindingValue :: Expr
  } deriving (Eq, Show)

data Definition
  = Data Identifier [Identifier] (NonEmpty ProdDecl)
  | TypeSignature Identifier TypeScheme
  | Function Binding

data Expr
  = Id Identifier
  | Lit Literal
  | Prod Identifier [Expr]
  | App Expr Expr
  | Abs Identifier Expr
  | Let Binding Expr
  | Rec Binding Expr
  | Case Expr (NonEmpty (Pattern,Expr))
  | Error String
  deriving (Eq, Show)
