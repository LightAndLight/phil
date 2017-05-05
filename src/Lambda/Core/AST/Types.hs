{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies    #-}

module Lambda.Core.AST.Types where

import Control.Exception
import GHC.Stack
import Lambda.Exception
import Data.Typeable (Typeable)

import Data.Bifunctor
import Data.Foldable
import qualified Data.Map as M
import Data.Map (Map)
import Data.Maybe
import Data.Monoid
import           Data.List                         (intercalate)
import           Data.Set                          (Set)
import qualified Data.Set                          as S


import           Lambda.Core.AST.Identifier
import           Lambda.Typecheck.Unification

data TyCon = FunCon | TypeCon Identifier deriving (Eq, Show, Ord)

data Type
  = TyVar Identifier
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
ctorAndArgs :: (HasCallStack, Applicative f, Monoid (f Type)) => Type -> (Identifier, f Type)
ctorAndArgs ty = go ty
  where
    go (TyCtor con) = (con, mempty)
    go (TyApp rest arg) = second (<> pure arg) $ go rest
    go _ = internalError (InvalidTypeException ty)

toType :: Foldable f => (Identifier, f Type) -> Type
toType (con, args) = foldl' TyApp (TyCtor con) args

toTypeTyVars :: (Foldable f, Functor f) => (Identifier, f Identifier) -> Type
toTypeTyVars (con, args) = foldl' TyApp (TyCtor con) $ TyVar <$> args

data TypeScheme = Forall (Set Identifier) [Type] Type deriving (Eq, Show)

instance Unify Type where
  type Variable Type = Identifier

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
renameTypeScheme :: Map Identifier Identifier -> TypeScheme -> TypeScheme
renameTypeScheme subs (Forall vars cons ty)
  = let subs' = Substitution . M.toList $ TyVar <$> subs
    in Forall
      (S.map (\var -> fromMaybe var $ M.lookup var subs) vars)
      (substitute subs' <$> cons)
      (substitute subs' ty)

-- | Gets the C from a type of format: C a_1 a_2 .. a_n
getCtor :: Type -> Maybe TyCon
getCtor (TyCon con) = Just con
getCtor (TyApp con _) = getCtor con
getCtor _ = Nothing

freeInType :: Type -> Set Identifier
freeInType (TyVar name) = S.singleton name
freeInType (TyApp con arg) = freeInType con `S.union` freeInType arg
freeInType _ = S.empty

freeInScheme :: TypeScheme -> Set Identifier
freeInScheme (Forall vars _ ty) = freeInType ty `S.difference` vars

nestedFunc :: Type -> String
nestedFunc ty@(TyFun _ _) = "(" ++ showType ty ++ ")"
nestedFunc ty = showType ty

nestedCon :: Type -> String
nestedCon ty@TyApp{} = "(" ++ showType ty ++ ")"
nestedCon ty = showType ty

showType :: Type -> String
showType (TyVar name) = name
showType (TyFun from to) = nestedFunc from ++ " -> " ++ showType to
showType (TyApp cons arg) = showType cons ++ " " ++ nestedCon arg
showType (TyCon FunCon) = "(->)"
showType (TyCon (TypeCon con)) = con

showConstraints :: [Type] -> String
showConstraints [] = ""
showConstraints cons
  = let cons' = intercalate ", " $ fmap showType cons
    in (if length cons > 1 then "(" ++ cons' ++ ")"
       else cons') ++ "=> "

showTypeScheme :: TypeScheme -> String
showTypeScheme (Forall vars cons ty)
  | vars == S.empty = showConstraints cons ++ showType ty
  | otherwise = unwords ("forall" : S.toList vars) ++ ". " ++ showConstraints cons ++ showType ty
