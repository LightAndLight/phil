{-# LANGUAGE RankNTypes      #-}
{-# LANGUAGE TemplateHaskell #-}

module Lambda.Core.AST.Lens where

import           Control.Lens
import           Data.Set        (Set)

import           Lambda.Core.AST

makePrisms ''Prim
makePrisms ''TyCon
makePrisms ''Type

_TyFun :: Prism' Type (Type,Type)
_TyFun = prism' (uncurry TyFun) $ \ty -> case ty of { TyFun from to -> Just (from,to); _ -> Nothing }

makePrisms ''TypeScheme

_Forall' :: Set Identifier -> Prism' TypeScheme Type
_Forall' vars = prism' (Forall vars) $
  \scheme -> case scheme of
    Forall vars' ty
      | vars == vars' -> Just ty
      | otherwise -> Nothing
    _ -> Nothing

makePrisms ''Literal

makePrisms ''Pattern
makePrisms ''Expr

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
