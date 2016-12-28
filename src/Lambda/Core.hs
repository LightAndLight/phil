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


nestedFunc :: Type -> String
nestedFunc ty@FunType{} = "(" ++ showType ty ++ ")"
nestedFunc ty = showType ty

nested :: Type -> String
nested ty@PolyType{} = "(" ++ showType ty ++ ")"
nested ty = nestedFunc ty

showType :: Type -> String
showType (TypeVar name) = name
showType (PrimType ty) = show ty
showType (FunType from to) = nestedFunc from ++ " -> " ++ showType to
showType (PolyType cons []) = cons
showType (PolyType cons args) = cons ++ " " ++ unwords (fmap nested args)

showTypeScheme :: TypeScheme -> String
showTypeScheme (Base ty) = showType ty
showTypeScheme (Forall name scheme) = "forall " ++ name ++ showTypeScheme' scheme
  where
    showTypeScheme' (Base ty) = ". " ++ showType ty
    showTypeScheme' (Forall name scheme) = " " ++ name ++ showTypeScheme' scheme

showLiteral :: Literal -> String
showLiteral (LitInt a) = show a
showLiteral (LitString a) = show a
showLiteral (LitChar a) = show a

showPattern :: Pattern -> String
showPattern (PatCon name args) = name ++ unwords args
showPattern (PatLit lit) = showLiteral lit

showValue :: Expr -> Maybe String
showValue (Id expr) = Just expr
showValue (Lit lit) = Just $ showLiteral lit
showValue (Abs name expr) = Just "<Function>"
showValue (Error message) = Just $ "Runtime Error: " ++ message
showValue (Prod name args) = unwords . (:) name <$> traverse showValue args
showValue e = error $ "Cannot show " ++ show e
