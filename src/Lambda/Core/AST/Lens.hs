{-# LANGUAGE RankNTypes      #-}
{-# LANGUAGE TemplateHaskell #-}

module Lambda.Core.AST.Lens where

import           Control.Lens
import           Data.Set              (Set)
import qualified Data.Set              as S (fromList)

import           Lambda.Core.AST
import           Lambda.Core.Typecheck

ast :: Prism' Expr () -> Expr
ast p = p # ()

makePrisms ''Prim
makePrisms ''TyCon
makePrisms ''Type

_TyFun :: Prism' Type (Type,Type)
_TyFun = prism' (uncurry TyFun) $ \ty -> case ty of { TyFun from to -> Just (from,to); _ -> Nothing }

_TyFun' :: Type -> Type -> Prism' Type ()
_TyFun' ty ty' = only $ TyFun ty ty'

makePrisms ''TypeScheme

_Forall' :: [Identifier] -> Prism' TypeScheme Type
_Forall' vars = prism' (Forall $ S.fromList vars) $
  \scheme -> case scheme of
    Forall vars' ty
      | S.fromList vars == vars' -> Just ty
      | otherwise -> Nothing
    _ -> Nothing

makePrisms ''Literal

makePrisms ''Pattern
makePrisms ''Expr
makePrisms ''Binding

_Binding' :: Identifier -> Prism' Binding Expr
_Binding' name = prism' (Binding name) $
  \(Binding name' e) -> if name == name' then Just e else Nothing

_Id' :: Identifier -> Prism' Expr ()
_Id' = only . Id

_Lit' :: Literal -> Prism' Expr ()
_Lit' = only . Lit

_Prod' :: Identifier -> Prism' Expr [Expr]
_Prod' name = prism' (Prod name) $
  \e -> case e of
    Prod name' es
      | name == name' -> Just es
      | otherwise -> Nothing
    _ -> Nothing

_Abs' :: Identifier -> Prism' Expr Expr
_Abs' name = prism' (Abs name) $
  \e -> case e of
    Abs name' e'
      | name == name' -> Just e'
      | otherwise -> Nothing
    _ -> Nothing
