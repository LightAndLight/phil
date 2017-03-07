{-# LANGUAGE PatternSynonyms #-}

module Lambda.Core.AST.Types where

import           Data.List                  (intercalate)
import           Data.Set                   (Set)
import qualified Data.Set                   as S

import           Lambda.Core.AST.Identifier

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
