{-# language FlexibleContexts #-}
module Lambda.Core.Typeclasses
  ( TypeclassEntry(..)
  , checkConstraints
  , equalUpToRenaming
  , elementUpToRenaming
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

newtype Dictionary = Dictionary { getDict :: [(NonEmpty Type, [Binding Expr])] }

data TypeclassEntry
  = TceInst (Set Type) Type
  | TceClass (Set Type) Type

-- forall a : Type, b : Type
-- case equalUpToRenaming a b of
--   Just subs => substitute subs b = a, substitute subs a = a
--   Nothing => true
equalUpToRenaming :: Type -> Type -> Maybe (Map Identifier Identifier)
equalUpToRenaming (TyVar name) (TyVar name')
  | name == name' = Just M.empty
  | otherwise = Just $ M.singleton name' name
equalUpToRenaming (TyApp con arg) (TyApp con' arg')
  | Just conSubs <- equalUpToRenaming con con'
  , Just argSubs <- equalUpToRenaming arg arg'
  , and (M.intersectionWith (==) conSubs argSubs) = Just $ conSubs `M.union` argSubs
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
entails context p pis = pis `S.isSubsetOf` p || all (entails' context p) pis
  where
    entails' [] _ _ = False
    entails' (TceClass p' pi:context) p pi'
      | Just subs <- pi' `elementUpToRenaming` p' = entails context p (S.singleton $ substitute (TyVar <$> subs) pi)
      | otherwise = entails' context p pi'
    entails' (TceInst p' pi:context) p pi'
      | Just subs <- pi' `equalUpToRenaming` pi = entails context p (S.map (substitute $ TyVar <$> subs) p')
      | otherwise = entails' context p pi'

class HasClasses s where
  classes :: Lens' s (Map Identifier ([Identifier], Set Type))

getImpl :: NonEmpty Type -> Dictionary -> [Binding Expr]
getImpl tys (Dictionary dict) = fromMaybe [] $ lookup tys dict

addImpl :: NonEmpty Type -> [Binding Expr] -> Dictionary -> Dictionary
addImpl tys impls (Dictionary dict) = Dictionary $ (tys, impls):dict

-- | Entailment relation: first ||- second
-- | i.e. The second set can be deduced from the first set
{-
entails
  :: ( HasClasses r
     , HasDictionaries r
     , MonadReader r m
     , AsSyntaxError e
     , MonadError e m
     ) => Set Type -> Set Type -> m ()
entails subs supers = for (S.toList subs) $ \sub -> do
  (subClassName, subClassArgs) <- asClassDef sub
  maybeClassDetails <- uses $ M.lookup subClassName
  case maybeClassDetails of
    Nothing -> _
    Just (args, superClasses)
      | length args == length subClassArgs -> do
          -- Assumption: the kinds of subClassArgs are correct match the kinds of args
          let subs = M.fromList (zip subClassArgs args)
          let (tyVarPredicates, rest) = partition isTyVarPredicate . S.toList $ S.map (substitute subs) superClasses
          where
            isTyVarPredicate (TyApp (TyCon _) (TyVar _)) = True
            isTyVarPredicate _ = False
      | otherwise -> error "entailment error: constructor had incorrect number of arguments"
      -}

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

checkClassInstance constraints constructor params impls = undefined
