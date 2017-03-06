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
  | Forall (Set Identifier) (Set Type) Type
  deriving (Eq, Show)

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
  -- | ADT Definition: type constructor, type variables, constructor definitions
  = Data Identifier [Identifier] (NonEmpty ProdDecl)
  -- | Type signature: function name, type
  | TypeSignature Identifier TypeScheme
  -- | Function definition
  | Function Binding
  -- | Class definition: constraints, class name, type variables, class members
  | Class (Set Type) Identifier [Identifier] [(Identifier, TypeScheme)]
  -- | Classs instance definition: constraints, class name, type arguments, member implementations
  | Instance (Set Type) Identifier [Type] [Binding]

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

showConstraints :: Set Type -> String
showConstraints cons
  | cons == S.empty = ""
  | otherwise
  = let cons' = intercalate ", " . fmap showType $ S.toList cons
    in (if length cons > 1 then "(" ++ cons' ++ ")"
       else cons') ++ "=> "

showTypeScheme :: TypeScheme -> String
showTypeScheme (Base ty) = showType ty
showTypeScheme (Forall vars cons ty) = unwords ("forall" : S.toList vars) ++ ". " ++ showConstraints cons ++ showType ty

showLiteral :: Literal -> String
showLiteral (LitInt a) = show a
showLiteral (LitString a) = show a
showLiteral (LitChar a) = show a
showLiteral (LitBool b) = if b then "true" else "false"

showPattern :: Pattern -> String
showPattern (PatId a) = a
showPattern (PatCon name args) = name ++ unwords args
showPattern (PatLit lit) = showLiteral lit
