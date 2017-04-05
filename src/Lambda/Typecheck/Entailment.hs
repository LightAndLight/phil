{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

module Lambda.Typecheck.Entailment
  ( entails
  , replacePlaceholders
  , resolvePlaceholders
  , simplify
  , updatePlaceholders
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
import           Lambda.Core.AST.InstanceHead
import           Lambda.Core.AST.Types
import           Lambda.Sugar
import           Lambda.Typecheck.TypeError
import           Lambda.Typecheck.Unification
import           Lambda.Typeclasses

applyMapping :: Map Placeholder Placeholder -> Placeholder -> Placeholder
applyMapping mapping ty = fromMaybe ty (M.lookup ty mapping)

updatePlaceholders :: Map Placeholder Placeholder -> Expr -> Expr
updatePlaceholders mapping = everywhere updatePlaceholder 
  where
    updatePlaceholder (DictPlaceholder p) = DictPlaceholder $ applyMapping mapping p
    updatePlaceholder a = a

-- | Reduce a list of predicates to a normal form where no predicate
-- | can be derived from the other predicates
-- |
-- | The resulting elements will retain their respective order
simplify
  :: [TypeclassEntry a] -- ^ Typeclass context
  -> [Type] -- ^ Predicates
  -> ([Type], Map Placeholder Placeholder) -- ^ New predicates, and a mapping from old placeholders to new placeholders
simplify ctxt preds = go [] $ reverse preds
  where
    entailedBy [] goal = Nothing
    entailedBy (pred : rest) goal
      | entails ctxt [pred] goal = Just pred
      | otherwise = entailedBy rest goal

    go seen [] = (seen, M.empty)
    go seen (pred : rest)
      | Just parent <- entailedBy (seen ++ rest) pred
      = let mapping =
              M.singleton
                (fmap N.fromList . fromJust $ ctorAndArgs pred)
                (fmap N.fromList . fromJust $ ctorAndArgs parent)
        in M.union mapping . fmap (applyMapping mapping) <$> go seen rest
      | otherwise = go (pred : seen) rest

-- | Given a typeclass context, does the knowledge base always imply the
-- | goal?
entails
  :: [TypeclassEntry a] -- ^ Typeclass context
  -> [Type] -- ^ Knowledge base
  -> Type -- ^ Goal
  -> Bool
entails ctxt kb goal = goal `elem` kb || go ctxt goal
  where
    go [] goal = False
    go (TceInst supers instHead _ : rest) goal
      | Right subs <- unify [(instHeadToType instHead, goal)]
      = all (entails ctxt kb) (substitute subs . toTypeTyVars <$> supers) || go rest goal
      | otherwise = go rest goal
    go (TceClass supers className classArgs _ _ : rest) goal
      | (subs : _) <- rights $ fmap (\ty -> unify [(toTypeTyVars ty, goal)]) supers
      = let classTy = foldl' TyApp (TyCtor className) $ substitute subs . TyVar <$> classArgs
        in entails ctxt kb classTy || go rest goal
      | otherwise = go rest goal

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
  -> [Placeholder] -- ^ Dictionary parameter environment
  -> Set Identifier -- ^ Type variables bound in the outer context
  -> m ([Placeholder], [(Placeholder, Expr)])
resolvePlaceholders ctxt [] _ = pure ([], [])
resolvePlaceholders ctxt (p@(con, args) : rest) bound
  | foldMap freeInType args `S.intersection` bound /= S.empty
  = first (p :) <$> resolvePlaceholders ctxt rest bound

  | any isTyVar args
  = do
    (leftover, mapping) <- resolvePlaceholders ctxt rest bound
    case lookup p mapping of
      Nothing -> do
        var <- ("dict" ++) <$> fresh
        pure (leftover, (p, DictVar var) : mapping)
      Just _ -> pure (leftover, mapping)

  | otherwise = go ctxt
  where
    toType (con, args) = foldl' TyApp (TyCtor con) $ TyVar <$> args
    inputTy = foldl' TyApp (TyCtor con) args

    go [] = throwError $ _NoSuchInstance # p
    go (TceClass supers className tyVars _ _ : entries)
      | (subs : _) <- rights $ fmap (\ty -> unify [(toTypeTyVars ty, inputTy)]) supers
      = flip catchError (const $ go entries) $ do
          let tyArgs = substitute subs . TyVar <$> tyVars
          (leftover, mapping) <- resolvePlaceholders ctxt ((className, tyArgs) : rest) bound
          case lookup (className, tyArgs) mapping of
            Nothing -> go entries
            Just dict ->
              pure (leftover, ((con, args), DictSuper className dict) : mapping)
      | otherwise = go entries

    go (TceInst supers instHead _ : entries)
      | con == instHead ^. ihClassName
      , Right subs <- unify .
          N.toList $
          N.zip (toType <$> instHead ^. ihInstArgs) args
      = do
        let supers' = over (mapped._2.mapped) (substitute subs . TyVar) supers
        (leftover, mapping) <-
          resolvePlaceholders
            ctxt
            (supers' ++ rest)
            bound
        let superDicts = traverse (`lookup` mapping) supers'
        case superDicts of
          Nothing -> throwError $ _NoSuchInstance # p
          Just supers -> do
            let args' = fromJust . ctorAndArgs <$> args :: NonEmpty (Identifier, [Type])
            let dict = foldl' App (DictInst con $ fst <$> args') supers
            pure (leftover, ((con, args), dict) : mapping)
      | otherwise = go entries

    newPlaceholders (con, args) = do
      ident <- ("dict" ++) <$> fresh
      pure (con, args)

    isTyVar TyVar{} = True
    isTyVar _ = False
