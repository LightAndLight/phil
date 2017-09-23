{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies    #-}
module Phil.Core.AST.Types where

import Control.Exception
import GHC.Stack
import Phil.Exception

import Data.Bifunctor
import Data.Foldable
import qualified Data.Map as M
import Data.Map (Map)
import Data.Maybe
import Data.Monoid
import Data.List (intersperse)
import Data.Text (unpack)
import Data.Typeable (Typeable)
import Data.Set (Set)
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>), (<>))

import qualified Data.Set as S


import Phil.Core.AST.Identifier
import Phil.Typecheck.Unification

data TyCon
  = FunCon
  | TypeCon Ctor
  deriving (Eq, Show, Ord)

data Type
  = TyVar Ident
  | TyApp Type Type
  | TyCon TyCon
  deriving (Eq, Show, Ord)

pattern TyFun from to = TyApp (TyApp (TyCon FunCon) from) to
pattern TyCtor con = TyCon (TypeCon con)

data TypeException
  = InvalidTypeException Type
  deriving (Show, Typeable)

instance Exception TypeException where

-- | Split a Type into a type constructor and some arguments
-- |
-- | Partial, throws a TypeException
ctorAndArgs :: (HasCallStack, Applicative f, Monoid (f Type)) => Type -> (Ctor, f Type)
ctorAndArgs ty = go ty
  where
    go (TyCtor con) = (con, mempty)
    go (TyApp rest arg) = second (<> pure arg) $ go rest
    go _ = internalError (InvalidTypeException ty)

toType :: Foldable f => (Ctor, f Type) -> Type
toType (con, args) = foldl' TyApp (TyCtor con) args

toTypeTyVars :: (Foldable f, Functor f) => (Ctor, f Ident) -> Type
toTypeTyVars (con, args) = foldl' TyApp (TyCtor con) $ TyVar <$> args

data TypeScheme = Forall (Set Ident) [Type] Type deriving (Eq, Show)

instance Unify Type where
  type Variable Type = Ident

  substitute (Substitution []) t = t
  substitute subs (TyApp t1 t2) = TyApp (substitute subs t1) (substitute subs t2)
  substitute (Substitution ((var, t') : rest)) t@(TyVar var')
    | var == var' = substitute (Substitution rest) t'
    | otherwise = substitute (Substitution rest) t
  substitute _ t = t

  implications (ty@TyVar{}, ty') = [(ty, ty')]
  implications (ty, ty'@TyVar{}) = [(ty', ty)]
  implications (TyApp t1 t2, TyApp t1' t2')
    = let t1i = implications (t1, t1')
          t2i = implications (t2, t2')
      in if null t1i || null t2i then [] else t1i ++ t2i
  implications c@(t1, t2)
    | t1 == t2 = [c]
    | otherwise = []

  occurs name (TyVar name') = name == name'
  occurs name (TyApp t1 t2) = occurs name t1 || occurs name t2
  occurs _ _ = False

  toVariable (TyVar name) = Just name
  toVariable _ = Nothing

-- | Apply a substitution to the free variables in a typescheme
subTypeScheme :: Substitution Type -> TypeScheme -> TypeScheme
subTypeScheme (Substitution subs) scheme = go (freeInScheme scheme) subs scheme
  where
    go frees [] scheme = scheme
    go frees (sub@(var, _):rest) scheme
      | not (var `S.member` frees) = go frees rest scheme
      | Forall vars cons ty <- scheme
      , let runSub = substitute (Substitution [sub])
      = go frees rest (Forall vars (fmap runSub cons) $ runSub ty)

-- | Rename the bound type variables in a type scheme
renameTypeScheme :: Map Ident Ident -> TypeScheme -> TypeScheme
renameTypeScheme subs (Forall vars cons ty)
  = let subs' = Substitution . M.toList $ TyVar <$> subs
    in Forall
      (S.map (\var -> fromMaybe var $ M.lookup var subs) vars)
      (substitute subs' <$> cons)
      (substitute subs' ty)

-- | Gets the C from a type of format: C a_1 a_2 .. a_n
extractCtor :: Type -> Maybe TyCon
extractCtor (TyCon con) = Just con
extractCtor (TyApp con _) = extractCtor con
extractCtor _ = Nothing

freeInType :: Type -> Set Ident
freeInType (TyVar name) = S.singleton name
freeInType (TyApp con arg) = freeInType con `S.union` freeInType arg
freeInType _ = S.empty

freeInScheme :: TypeScheme -> Set Ident
freeInScheme (Forall vars _ ty) = freeInType ty `S.difference` vars

renderType :: Type -> Doc
renderType (TyVar name) = text . unpack $ getIdent name
renderType (TyFun from to) =
  nestedFunc from <>
  space <> text "->" <> space <>
  renderType to
  where
    nestedFunc ty@(TyFun _ _) = parens $ renderType ty
    nestedFunc ty = renderType ty
renderType (TyApp cons arg) = renderType cons <> space <> nestedCon arg
  where
    nestedCon ty@TyApp{} = parens $ renderType ty
    nestedCon ty = renderType ty
renderType (TyCon FunCon) = text "(->)"
renderType (TyCon (TypeCon con)) = text . unpack $ getCtor con

renderConstraints :: [Type] -> Doc
renderConstraints [] = mempty
renderConstraints cs
  = let cons' = fold . intersperse (comma <> space) $ fmap renderType cs
    in
      if length cs > 1
      then parens cons'
      else cons'

renderTypeScheme :: TypeScheme -> Doc
renderTypeScheme (Forall vars cons ty)
  | vars == S.empty = renderConstraints cons <> renderType ty
  | otherwise =
      text "forall" <> space <>
      fold (intersperse space . fmap (text . unpack . getIdent) $ S.toList vars)
      <> text "." <> space <>
      renderConstraints cons <>
      (if null cons then mempty else text "=>" <> space) <>
      renderType ty
