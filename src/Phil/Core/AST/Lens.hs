{-# LANGUAGE RankNTypes      #-}
{-# LANGUAGE TemplateHaskell #-}

module Phil.Core.AST.Lens where

import           Control.Lens
import           Control.Monad.Except
import           Data.Set                   (Set)
import qualified Data.Set                   as S (fromList)

import           Phil.Core.AST.Binding
import           Phil.Core.AST.Expr
import           Phil.Core.AST.Identifier
import           Phil.Core.AST.Literal
import           Phil.Core.AST.Pattern
import           Phil.Core.AST.Types

ast :: Prism' Expr () -> Expr
ast p = p # ()

makePrisms ''TyCon
makePrisms ''Type

_TyFun :: Prism' Type (Type,Type)
_TyFun = prism' (uncurry TyFun) $ \ty -> case ty of { TyFun from to -> Just (from,to); _ -> Nothing }

_TyFun' :: Type -> Type -> Prism' Type ()
_TyFun' ty ty' = only $ TyFun ty ty'

_TyCtor :: Prism' Type Identifier
_TyCtor = prism' TyCtor $ \ty -> case ty of { TyCtor con -> Just con; _ -> Nothing }

makePrisms ''TypeScheme

_Forall' :: [Identifier] -> [Type] -> Prism' TypeScheme Type
_Forall' vars cons = prism' (Forall (S.fromList vars) cons) $
  \scheme -> case scheme of
    Forall vars' cons' ty
      | S.fromList vars == vars' && cons == cons' -> Just ty
      | otherwise -> Nothing
    _ -> Nothing

makePrisms ''Literal

makePrisms ''Pattern
makePrisms ''Expr
makePrisms ''Binding

_Binding' :: Identifier -> Prism' (Binding Expr) Expr
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
