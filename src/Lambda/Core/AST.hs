{-# LANGUAGE PatternSynonyms #-}

module Lambda.Core.AST where

import           Data.List
import           Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as N
import           Data.Set           (Set)
import qualified Data.Set           as S

data Prim
  = Int
  | String
  | Char
  | Bool
  deriving (Eq, Show, Ord)

data TyCon = FunCon | TypeCon Identifier deriving (Eq, Show, Ord)

data Type
  = TyVar String
  | TyApp Type Type
  | TyCon TyCon
  | TyPrim Prim
  deriving (Eq, Show, Ord)

pattern TyFun from to = TyApp (TyApp (TyCon FunCon) from) to

data TypeScheme
  = Base Type
  | Forall (Set Identifier) Qualified
  deriving (Eq, Show)

data Qualified = Qualified (Set Type) Type deriving (Eq, Show)

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

nestedFunc :: Type -> String
nestedFunc ty@(TyFun _ _) = "(" ++ showType ty ++ ")"
nestedFunc ty = showType ty

nestedCon :: Type -> String
nestedCon ty@TyApp{} = "(" ++ showType ty ++ ")"
nestedCon ty = showType ty

showType :: Type -> String
showType (TyVar name) = name
showType (TyPrim ty) = show ty
showType (TyFun from to) = nestedFunc from ++ " -> " ++ showType to
showType (TyApp cons arg) = showType cons ++ " " ++ nestedCon arg
showType (TyCon FunCon) = "(->)"
showType (TyCon (TypeCon con)) = con

showPredicates :: Set Type -> String
showPredicates preds
  = let preds' = intercalate ", " . fmap showType $ S.toList preds
    in if length preds > 1 then "(" ++ preds' ++ ")"
       else preds'

showQualified :: Qualified -> String
showQualified (Qualified preds ty) = showPredicates preds ++ "=> " ++ showType ty

showTypeScheme :: TypeScheme -> String
showTypeScheme (Base ty) = showType ty
showTypeScheme (Forall vars qual) = unwords ("forall" : S.toList vars) ++ ". " ++ showQualified qual

showLiteral :: Literal -> String
showLiteral (LitInt a) = show a
showLiteral (LitString a) = show a
showLiteral (LitChar a) = show a
showLiteral (LitBool b) = if b then "true" else "false"

showPattern :: Pattern -> String
showPattern (PatId a) = a
showPattern (PatCon name args) = name ++ unwords args
showPattern (PatLit lit) = showLiteral lit
