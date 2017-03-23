{-# language FlexibleContexts #-}
module Lambda.Core.Typeclasses
  ( HasTcContext(..)
  , TypeclassEntry(..)
  , buildDictionary
  , checkConstraints
  , equalUpToRenaming
  , elementUpToRenaming
  , getClass
  , getInst
  , entails
  ) where

import Control.Lens
import Control.Applicative
import Data.Bifunctor
import Control.Monad.Except
import Control.Monad.Reader
import Data.Traversable
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
import           Lambda.Core.AST.Evidence
import           Lambda.Core.AST.Identifier
import           Lambda.Core.AST.Types
import           Lambda.Core.Kinds
import Lambda.Sugar (AsSyntaxError(..), asClassDef)
import Lambda.Core.Typecheck.Unification

data TypeclassEntry
  = TceInst [Type] Type (Map Identifier Expr)
  | TceClass [Type] Type (Map Identifier TypeScheme)
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
elementUpToRenaming :: Type -> [Type] -> Maybe (Substitution Type)
elementUpToRenaming ty tys = asum $ fmap (equalUpToRenaming ty) tys

entails
  :: (HasEVarCount s, MonadState s m)
  => [TypeclassEntry]
  -> [(EVar, Type)]
  -> (EVar, Type)
  -> m (Maybe Dictionary)
entails ctxt p pi
  | fst pi `S.member` S.fromList (fst <$> p) = fmap fst <$> entails' ctxt (first Variable <$> p) pi
  | otherwise = pure Nothing
  where
    findPred :: (EVar, Type) -> [(Dictionary, Type)] -> Maybe (Dictionary, [(EVar, Dictionary)])
    findPred (var, ty) = go
      where
        go [] = Nothing
        go ((dict, ty') : rest)
          | ty == ty' = Just (dict, [(var, dict)])
          | otherwise = go rest

    entails' :: (HasEVarCount s, MonadState s m) => [TypeclassEntry] -> [(Dictionary, Type)] -> (EVar, Type) -> m (Maybe (Dictionary, [(EVar, Dictionary)]))
    entails' tctxt p pi' = case tctxt of
          [] -> pure $ findPred pi' p
          (TceClass p' pi _ : context)
            | Just subs <- elementUpToRenaming (snd pi') p' -> do
                let newPi = substitute subs pi
                eVar <- freshEVar
                res <- entails' ctxt (fmap (second $ substitute subs) p) (eVar, newPi)
                case res of
                  Just (dict, dSubs) -> pure $ Just (Select dict (snd pi'), dSubs)
                  Nothing -> entails' context p pi'
            | otherwise -> entails' context p pi'
          (TceInst p' pi _ : context)
            | Just subs <- equalUpToRenaming (snd pi') pi -> do
                p'eVars <- for p' $ \p -> (,) <$> freshEVar <*> pure p
                res <- traverse
                  (entails' ctxt $ fmap (second $ substitute subs) p)
                  (fmap (second $ substitute subs) p'eVars)
                case sequence res of
                  Just dicts -> do
                    let dSubs = join $ fmap snd dicts
                    let runSubs d = foldr subDict d dSubs
                    pure $ Just (Construct (Dict . substitute subs $ snd pi') $ fmap (runSubs . fst) dicts, dSubs)
                  Nothing -> entails' context p pi'
            | otherwise -> entails' context p pi'

buildDictionary
  :: (HasEVarCount s, MonadState s m)
  => [TypeclassEntry]
  -> [(EVar, Type)]
  -> (EVar, Type)
  -> m (Maybe (EVar, Dictionary))
buildDictionary tctxt cons ty = fmap ((,) $ fst ty) <$> entails tctxt cons ty

checkConstraints
  :: ( AsKindError e
     , MonadError e m
     , HasKindTable r
     , MonadReader r m
     , HasFreshCount s
     , MonadState s m
     ) => [Type] -> m (Substitution Kind)
checkConstraints [] = pure mempty
checkConstraints [con] = do
  (subs, k) <- inferKind con
  either (throwError . review _KUnificationError) (const $ pure subs) $ unify [(k, Constraint)]
checkConstraints (con:rest) = do
  subs <- checkConstraints [con]
  subs' <- local (over kindTable $ subKindTable subs) $ checkConstraints rest
  pure $ subs' <> subs
