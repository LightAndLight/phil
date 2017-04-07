{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

module Lambda.Typecheck.Entailment
  ( entails
  , resolvePlaceholder
  , resolveAllPlaceholders
  , simplify
  ) where

import           Control.Applicative
import Control.Lens
import Control.Monad.Except
import Control.Monad.Fresh
import Control.Monad.State
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

-- | Reduce a list of predicates to a normal form where no predicate
-- | can be derived from the other predicates
-- |
-- | The resulting elements will retain their respective order
simplify
  :: [TypeclassEntry a] -- ^ Typeclass context
  -> [Type] -- ^ Predicates
  -> [Type]
simplify ctxt preds = go [] $ reverse preds
  where
    entailedBy [] goal = Nothing
    entailedBy (pred : rest) goal
      | entails ctxt [pred] goal = Just pred
      | otherwise = entailedBy rest goal

    go seen [] = seen
    go seen (pred : rest)
      | Just parent <- entailedBy (seen ++ rest) pred
      = go seen rest
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
    go (TceClass supers className classArgs _ : rest) goal
      | (subs : _) <- rights $ fmap (\ty -> unify [(toTypeTyVars ty, goal)]) supers
      = let classTy = foldl' TyApp (TyCtor className) $ substitute subs . TyVar <$> classArgs
        in entails ctxt kb classTy || go rest goal
      | otherwise = go rest goal

-- | Replace the 'DictPlaceholder's in an expression using the specified
-- | mapping
replacePlaceholders :: Map Placeholder Expr -> Expr -> Expr
replacePlaceholders mapping expr@(DictPlaceholder d)
  | Just expr' <- M.lookup d mapping = expr'
  | otherwise = expr 
replacePlaceholders _ expr = expr

-- | Resolve as many placeholders as possible in the given expression.
-- |
-- | If the list of returned placeholders is empty, the resulting
-- | expression should contain no more placeholder nodes (ie. no
-- | placeholders were deferred
resolveAllPlaceholders
  :: ( MonadFresh m
     , AsTypeError e
     , MonadError e m
     )
  => Bool -- ^ Defer errors?
  -> [TypeclassEntry a] -- ^ Typeclass environment
  -> Set Identifier -- ^ Type variables bound in the outer context
  -> [(Placeholder, Maybe Expr)] -- ^ Dictionary parameter environment
  -> Expr -- ^ Target expression
  -> m ([Placeholder], [Identifier], Expr) -- ^ Deferred placeholders, dictionary variables, resulting expression
resolveAllPlaceholders shouldDeferErrors ctxt bound env expr = do
  (expr, (deferred, env')) <- runStateT (everywhereM go expr) ([], M.fromList env)
  let resolved = M.foldrWithKey justs M.empty env'
  pure
    ( deferred
    , foldr fromDictVar [] resolved
    , everywhere (replacePlaceholders resolved) expr
    )
  where
    justs k (Just v) rest = M.insert k v rest
    justs _ Nothing as = as

    fromDictVar (DictVar a) as = a : as
    fromDictVar _ as = as

    go (DictPlaceholder p) = do
      env <- gets snd
      result <- resolvePlaceholder shouldDeferErrors ctxt bound (M.toList env) p
      case result of
        Nothing -> do
          modify $ first (p :)
          pure $ DictPlaceholder p
        Just replacement -> do
          modify $ second (M.insert p $ Just replacement)
          pure replacement
    go expr = pure expr

-- | Construct a dictionary for a placeholder in terms of some others
-- |
-- | Returns Nothing if the dictionary construction must be deferred
resolvePlaceholder
  :: ( MonadFresh m
     , AsTypeError e
     , MonadError e m
     )
  => Bool -- ^ Defer errors?
  -> [TypeclassEntry a] -- ^ Typeclass environment
  -> Set Identifier -- ^ Type variables bound in the outer context
  -> [(Placeholder, Maybe Expr)] -- ^ Dictionary parameter environment
  -> Placeholder -- ^ The placeholder to construct a dictionary for
  -> m (Maybe Expr)
resolvePlaceholder shouldDeferErrors ctxt bound env goal@(con, args)
  | goal `elem` fmap fst env
  , foldMap freeInType args `S.intersection` bound /= S.empty
  = pure Nothing

  | Just value <- lookup goal env
  , any isTyVar args
  = case value of
      Nothing -> Just . DictVar . ("dict" ++) <$> fresh
      Just expr -> pure $ Just expr

  | otherwise = go ctxt
  where
    inputTy = toType goal

    go []
      | shouldDeferErrors = pure Nothing
      | otherwise = throwError $ _NoSuchInstance # goal

    go (TceClass supers className tyVars _ : entries)
      | ((superName, subs) : _) <-
        rights . zipWith (\a b -> (,) (fst a) <$> b) supers $ (\ty -> unify [(toTypeTyVars ty, inputTy)]) <$> supers
      = flip catchError (const $ go entries) $ do
          let tyArgs = substitute subs . TyVar <$> tyVars
          res <- resolvePlaceholder shouldDeferErrors ctxt bound env (className, tyArgs)
          pure $ DictSuper superName <$> res
      | otherwise = go entries

    go (TceInst supers instHead _ : entries)
      | con == instHead ^. ihClassName
      , Right subs <- unify .
          N.toList $
          N.zip (toTypeTyVars <$> instHead ^. ihInstArgs) args
      = flip catchError (const $ go entries) $ do
          let supers' = over (mapped._2.mapped) (substitute subs . TyVar) supers
          res <- traverse (resolvePlaceholder shouldDeferErrors ctxt bound env) supers'
          pure $ do
            res' <- sequence res
            let args' = ctorAndArgs <$> args :: NonEmpty (Identifier, [Type])
            pure $ foldl' App (DictInst con $ fst <$> args') res'
      | otherwise = go entries

    isTyVar TyVar{} = True
    isTyVar _ = False
