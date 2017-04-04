{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}

module Lambda.Typecheck.Entailment
  ( DictParamEntry(..), dpeClassName, dpeTyArgs, dpeDictVar 
  , entails
  , replacePlaceholders
  , resolvePlaceholders
  ) where

import           Control.Applicative
import Control.Lens
import Control.Monad.Fresh
import           Data.Bifunctor
import Data.List.NonEmpty (NonEmpty)
import qualified Data.Map as M
import Data.Map (Map)
import           Data.Foldable
import           Data.Maybe
import           Data.Semigroup
import qualified Data.Set as S
import Data.Set (Set)

import Lambda.AST
import Lambda.AST.Expr
import           Lambda.Core.AST.Identifier
import           Lambda.Core.AST.Types
import           Lambda.Sugar
import           Lambda.Typecheck.Unification
import           Lambda.Typeclasses

reduceContext
  :: [TypeclassEntry a]
  -> [Type]
  -> Type
  -> Maybe ([Type], Type)
reduceContext entries context (TyVar name) = Just (context, TyVar name)
reduceContext entries context ty = undefined
  where
    propagateClassTycon cls ty
      = let InstanceHead name args = asClassInstanceP ty
        in undefined

entails :: [TypeclassEntry a] -> [Type] -> Type -> Bool
entails ctxt kb goal = goal `elem` kb || go ctxt goal
  where
    go [] goal = False
    go (TceInst supers instHead _ : rest) goal
      | Right subs <- unify [(instHeadToType instHead, goal)]
      = all (entails ctxt kb) $ substitute subs <$> supers
      | otherwise = go rest goal
    go (TceClass supers className classArgs _ : rest) goal
      | Right (subs : _) <- traverse (\ty -> unify [(ty, goal)]) supers
      = let classTy = foldl' TyApp (TyCtor className) $ substitute subs . TyVar <$> classArgs
        in entails ctxt kb classTy || go rest goal
      | otherwise = go rest goal

data DictParamEntry
  = DictParamEntry
  { _dpeClassName :: Identifier
  , _dpeTyArgs :: NonEmpty Type
  , _dpeDictVar :: Identifier
  } deriving (Eq, Ord, Show)

makeLenses ''DictParamEntry

-- | Replace the 'DictPlaceholder's in an expression using the specified
-- | mapping
replacePlaceholders :: Map (Identifier, NonEmpty Type) Expr -> Expr -> Expr
replacePlaceholders mapping expr@(DictPlaceholder d)
  | Just expr' <- M.lookup d mapping = expr'
  | otherwise = expr 
replacePlaceholders _ expr = expr

resolvePlaceholders
  :: MonadFresh m
  => [TypeclassEntry a] -- ^ Typeclass environment
  -> [DictParamEntry] -- ^ Dictionary parameter environment
  -> Set Identifier -- ^ Type variables bound in the outer context
  -> m ([DictParamEntry], [((Identifier, NonEmpty Type), Expr)])
resolvePlaceholders ctxt [] _ = pure ([], [])
resolvePlaceholders ctxt (p : rest) bound
  | foldMap freeInType (_dpeTyArgs p) `S.intersection` bound /= S.empty
  = first (p :) <$> resolvePlaceholders ctxt rest bound
  | any isTyVar (_dpeTyArgs p)
  = do
    (leftover, mapping) <- resolvePlaceholders ctxt rest bound
    let placeholder = (_dpeClassName p, _dpeTyArgs p)
    case lookup placeholder mapping of
      Nothing -> do
        var <- ("dict" ++) <$> fresh
        pure (leftover, (placeholder, DictVar var) : mapping)
      Just _ -> pure (leftover, mapping)
  | Just (subs, TceInst supers instHead impls) <- getInst ctxt (_dpeClassName p) (_dpeTyArgs p)
  = do
    new <- traverse (newPlaceholders . ctorAndArgs . substitute subs) supers
    let inst = DictInst (instHead ^. ihClassName) (fst <$> instHead ^. ihInstArgs)
    let dictExpr = foldl' App inst (fmap (\n -> DictPlaceholder (_dpeClassName n, _dpeTyArgs n)) new)
    (leftover, mapping) <- resolvePlaceholders ctxt (new ++ rest) bound
    let dictExpr' = everywhere (replacePlaceholders $ M.fromList mapping) dictExpr
    pure (leftover, ((_dpeClassName p, _dpeTyArgs p), dictExpr') : mapping)
  where
    newPlaceholders (con, args) = do
      ident <- ("dict" ++) <$> fresh
      pure $ DictParamEntry con args ident

    isTyVar TyVar{} = True
    isTyVar _ = False

    ctorAndArgs (TyApp (TyCtor con) arg) = (con, pure arg)
    ctorAndArgs (TyApp rest arg)
      = let (con, args) = ctorAndArgs rest
        in (con, args <> pure arg)
