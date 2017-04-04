{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}

module Lambda.Typecheck.Entailment
  ( DictParamEntry(..), dpeClassName, dpeTyArgs
  , entails
  , replacePlaceholders
  , resolvePlaceholders
  ) where

import           Control.Applicative
import Control.Lens
import Control.Monad.Except
import Control.Monad.Fresh
import           Data.Bifunctor
import Data.Either
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as N
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
import           Lambda.Typecheck.TypeError
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
      | (subs : _) <- rights $ fmap (\ty -> unify [(ty, goal)]) supers
      = let classTy = foldl' TyApp (TyCtor className) $ substitute subs . TyVar <$> classArgs
        in entails ctxt kb classTy || go rest goal
      | otherwise = go rest goal

data DictParamEntry
  = DictParamEntry
  { _dpeClassName :: Identifier
  , _dpeTyArgs :: NonEmpty Type
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
  :: ( MonadFresh m
     , AsTypeError e
     , MonadError e m
     )
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

  | otherwise = go ctxt
  where
    toType (con, args) = foldl' TyApp (TyCtor con) $ TyVar <$> args
    inputTy = foldl' TyApp (TyCtor $ p ^. dpeClassName) (p ^. dpeTyArgs)

    go [] = throwError $ _NoSuchInstance # (p ^. dpeClassName, p ^. dpeTyArgs)
    go (TceClass supers className tyVars _ : entries)
      | (subs : _) <- rights $ fmap (\ty -> unify [(ty, inputTy)]) supers
      = flip catchError (const $ go entries) $ do
          let tyArgs = substitute subs . TyVar <$> tyVars
          (leftover, mapping) <- resolvePlaceholders ctxt (DictParamEntry className tyArgs : rest) bound
          case lookup (className, tyArgs) mapping of
            Nothing -> go entries
            Just dict ->
              pure (leftover, ((p ^. dpeClassName, p ^. dpeTyArgs), DictSuper className dict) : mapping)
      | otherwise = go entries

    go (TceInst supers instHead _ : entries)
      | p ^. dpeClassName == instHead ^. ihClassName
      , Right subs <- unify .
          N.toList $
          N.zip
            (toType <$> instHead ^. ihInstArgs)
            (p ^. dpeTyArgs)
      = do
        let Just supers' = traverse (fmap (second N.fromList) . ctorAndArgs . substitute subs) supers
        (leftover, mapping) <-
          resolvePlaceholders
            ctxt
            (fmap (uncurry DictParamEntry) supers' ++ rest)
            bound
        let superDicts = traverse (`lookup` mapping) supers'
        case superDicts of
          Nothing -> throwError $ _NoSuchInstance # (p ^. dpeClassName, p ^. dpeTyArgs)
          Just supers -> do
            let dict = foldl' App (DictInst (p ^. dpeClassName) (fst . fromJust . ctorAndArgs <$> p ^. dpeTyArgs)) supers
            pure (leftover, ((p ^. dpeClassName, p ^. dpeTyArgs), dict) : mapping)
      | otherwise = go entries

    newPlaceholders (con, args) = do
      ident <- ("dict" ++) <$> fresh
      pure $ DictParamEntry con args

    isTyVar TyVar{} = True
    isTyVar _ = False
