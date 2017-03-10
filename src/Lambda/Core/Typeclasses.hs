{-# language FlexibleContexts #-}
module Lambda.Core.Typeclasses
  ( HasTcContext(..)
  , TypeclassEntry(..)
  , checkConstraints
  , equalUpToRenaming
  , elementUpToRenaming
  , getClass
  , subsetUpToRenaming
  , entails
  ) where

import Control.Lens
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Foldable
import qualified Data.Set as S
import Data.Maybe
import qualified Data.Map as M
import Data.Map (Map)
import Data.List.NonEmpty (NonEmpty)
import Data.Set (Set)

import           Lambda.Core.AST.Binding
import           Lambda.Core.AST.Expr
import           Lambda.Core.AST.Identifier
import           Lambda.Core.AST.Types
import           Lambda.Core.Kinds
import Lambda.Core.Typecheck.Substitution
import Lambda.Sugar (AsSyntaxError(..), asClassDef)

data TypeclassEntry
  = TceInst (Set Type) Type
  | TceClass (Set Type) Type (Map Identifier TypeScheme)
  deriving (Eq, Show)

getClass :: Identifier -> [TypeclassEntry] -> Maybe TypeclassEntry
getClass _ [] = Nothing
getClass className (entry@(TceClass _ clsTy _):rest)
  | Just (TypeCon className') <- getConstructor clsTy
  , className == className' = Just entry
  | otherwise = getClass className rest

class HasTcContext s where
  tcContext :: Lens' s [TypeclassEntry]

-- forall a : Type, b : Type
-- case equalUpToRenaming a b of
--   Just subs => substitute subs b = a, substitute subs a = a
--   Nothing => true
equalUpToRenaming :: Type -> Type -> Maybe (Map Identifier Identifier)
equalUpToRenaming (TyVar name) (TyVar name')
  | name == name' = Just M.empty
  | otherwise = Just $ M.singleton name' name
equalUpToRenaming ty@(TyApp con arg) ty'@(TyApp con' arg')
  | Just conSubs <- equalUpToRenaming con con'
  , Just argSubs <- equalUpToRenaming arg arg'
  , and (M.intersectionWith (==) conSubs argSubs)
  , freeInType ty `S.intersection` freeInType ty' == S.empty = Just $ conSubs `M.union` argSubs
  | otherwise = Nothing
equalUpToRenaming ty ty'
  | ty == ty' = Just M.empty
  | otherwise = Nothing

-- forall a : Type, b : Set Type
-- case elementUpToRenaming a b of
--   Just subs => a `S.member` S.map (substitute subs) b, substitute subs a = a
--   Nothing => true
elementUpToRenaming :: Type -> Set Type -> Maybe (Map Identifier Identifier)
elementUpToRenaming ty tys = asum . fmap (equalUpToRenaming ty) $ S.toList tys

-- forall a : Set Type, b : Set Type
-- case subsetUpToRenaming a b of
--   Just subs => a `S.isSubsetOf` S.map (substitute subs) b, S.map (substitute subs) a = a
--   Nothing => true
subsetUpToRenaming :: Set Type -> Set Type -> Maybe (Map Identifier Identifier)
subsetUpToRenaming sub super = go (S.toList sub) super M.empty
  where
    go [] super renamings = Just renamings
    go (ty:rest) super renamings
      | Just subs <- elementUpToRenaming ty super
      , and (M.intersectionWith (==) renamings subs) = go rest super (M.union renamings subs)
      | otherwise = Nothing

entails :: [TypeclassEntry] -> Set Type -> Set Type -> Bool
entails ctxt p pis = pis `S.isSubsetOf` p || all (entails' ctxt p) pis
  where
    entails' [] _ _ = False
    entails' (TceClass p' pi _ : context) p pi'
      | Just subs <- pi' `elementUpToRenaming` p', entails context p (S.singleton $ substitute (TyVar <$> subs) pi) = True
      | otherwise = entails' context p pi'
    entails' (TceInst p' pi:context) p pi'
      | Just subs <- pi `equalUpToRenaming` pi', entails context p (S.map (substitute $ TyVar <$> subs) p') = True
      | otherwise = entails' context p pi'

checkConstraints
  :: ( AsKindError e
     , MonadError e m
     , HasKindTable r
     , MonadReader r m
     , HasFreshCount s
     , MonadState s m
     ) => S.Set Type -> m (M.Map Identifier Kind)
checkConstraints = go . S.toList
  where
    go [] = pure M.empty
    go [con] = do
      (subs, k) <- inferKind con
      unifyKinds [(k, Constraint)]
      pure subs
    go (con:rest) = do
      subs <- go [con]
      subs' <- local (over kindTable $ subKindTable subs) $ go rest
      pure $ applyKindSubs subs' subs
