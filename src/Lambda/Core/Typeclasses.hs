{-# language FlexibleContexts #-}
module Lambda.Core.Typeclasses
  ( HasTcContext(..)
  , TypeclassEntry(..)
  , checkConstraints
  , equalUpToRenaming
  , elementUpToRenaming
  , getClass
  , getInst
  , subsetUpToRenaming
  , entails
  ) where

import Control.Lens
import Control.Applicative
import Data.Bifunctor
import Control.Monad.Except
import Control.Monad.Reader
import Data.Monoid
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
import Lambda.Sugar (AsSyntaxError(..), asClassDef)
import Lambda.Core.Typecheck.Unification

data TypeclassEntry
  = TceInst (Set Type) Type (Map Identifier Expr)
  | TceClass (Set Type) Type (Map Identifier TypeScheme)
  deriving (Eq, Show)

getClass :: Identifier -> [TypeclassEntry] -> Maybe TypeclassEntry
getClass _ [] = Nothing
getClass className (entry@(TceClass _ clsTy _):rest)
  | Just (TypeCon className') <- getConstructor clsTy
  , className == className' = Just entry
  | otherwise = getClass className rest
getClass className (_:rest) = getClass className rest

getInst :: Type -> [TypeclassEntry] -> Maybe TypeclassEntry
getInst _ [] = Nothing
getInst inst (entry@(TceInst _ instTy _) : rest)
  | inst == instTy = Just entry
  | otherwise = getInst inst rest
getInst inst (_ : rest) = getInst inst rest

class HasTcContext s where
  tcContext :: Lens' s [TypeclassEntry]

-- forall a : Type, b : Type
-- case equalUpToRenaming a b of
--   Just subs => substitute subs b = substitute subs a
--   Nothing => true
equalUpToRenaming :: Type -> Type -> Maybe (Substitution Type)
equalUpToRenaming ty ty' = either (const Nothing) Just $ unify [(ty, ty')]

-- forall a : Type, b : Set Type
-- case elementUpToRenaming a b of
--   Just subs => substitute subs a `S.member` S.map (substitute subs) b
--   Nothing => true
elementUpToRenaming :: Type -> Set Type -> Maybe (Substitution Type)
elementUpToRenaming ty tys = asum . fmap (equalUpToRenaming ty) $ S.toList tys

-- forall a : Set Type, b : Set Type
-- case subsetUpToRenaming a b of
--   Just subs => S.map (substitute subs a) `S.isSubsetOf` S.map (substitute subs) b
--   Nothing => true
subsetUpToRenaming :: Set Type -> Set Type -> Maybe (Substitution Type)
subsetUpToRenaming sub = go mempty (S.toList sub)
  where
    go :: Substitution Type -> [Type] -> Set Type -> Maybe (Substitution Type)
    go subs [] super = Just subs
    go subs (ty:rest) super = do
      let super' = S.map (substitute subs) super
      subs' <- elementUpToRenaming (substitute subs ty) super'
      liftA2 (<>) (go (subs' <> subs) rest super') $ pure subs'

entails :: [TypeclassEntry] -> Set Type -> Type -> Bool
entails ctxt p pi = entails' ctxt p pi
  where
    entails' tctxt p pi'
      | S.member pi' p = True
      | otherwise = case tctxt of
          [] -> False
          (TceClass p' pi _ : context)
            | Just subs <- elementUpToRenaming pi' p'
            , entails' ctxt (S.map (substitute subs) p) (substitute subs pi) -> True
            | otherwise -> entails' context p pi'
          (TceInst p' pi _ : context)
            | Just subs <- equalUpToRenaming pi' pi
            , all (entails' ctxt $ S.map (substitute subs) p) (S.map (substitute subs) p')
            -> True
            | otherwise -> entails' context p pi'

checkConstraints
  :: ( AsKindError e
     , MonadError e m
     , HasKindTable r
     , MonadReader r m
     , HasFreshCount s
     , MonadState s m
     ) => S.Set Type -> m (Substitution Kind)
checkConstraints = go . S.toList
  where
    go [] = pure mempty
    go [con] = do
      (subs, k) <- inferKind con
      either (throwError . review _KUnificationError) (const $ pure subs) $ unify [(k, Constraint)]
    go (con:rest) = do
      subs <- go [con]
      subs' <- local (over kindTable $ subKindTable subs) $ go rest
      pure $ subs' <> subs
