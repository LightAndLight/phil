{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

module Lambda.Typecheck.Entailment
  ( entails
  , resolvePlaceholder
  , resolveAllPlaceholders
  , simplify
  ) where

import Control.Applicative
import Control.Lens
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Bifunctor
import Data.Either
import Data.Foldable
import Data.List.NonEmpty (NonEmpty)
import Data.Map (Map)
import Data.Maybe
import Data.Semigroup
import Data.Set (Set)

import qualified Data.List.NonEmpty as N
import qualified Data.Map as M
import qualified Data.Set as S

import Lambda.AST
import Lambda.AST.Expr
import Lambda.Core.AST.Identifier
import Lambda.Core.AST.InstanceHead
import Lambda.Core.AST.Types
import Lambda.ModuleInfo
import Lambda.Sugar
import Lambda.Typecheck.TC
import Lambda.Typecheck.TypeError
import Lambda.Typecheck.Unification
import Lambda.Typeclasses

-- | Rename all the type variables in a class / instance declaration to fresh
-- | and return the substitution that was created
standardizeApart
  :: TypeclassEntry a
  -> TC e (Map Identifier Identifier, TypeclassEntry a)
standardizeApart entry = case entry of
  TceInst modName supers instHead impls -> do
    let frees = foldr S.insert S.empty . fold $ snd <$> (instHead ^. ihInstArgs)
    subs <- makeSubs frees
    let inst = TceInst
          modName
          (over (mapped._2.mapped) (fromMapping subs) supers)
          (over (ihInstArgs.mapped._2.mapped) (fromMapping subs) instHead)
          impls
    pure (subs, inst)
  TceClass supers className tyArgs members -> do
    let frees = foldr S.insert S.empty tyArgs
    subs <- makeSubs frees 
    let cls = TceClass
          (over (mapped._2.mapped) (fromMapping subs) supers)
          className
          (fromMapping subs <$> tyArgs)
          (renameTypeScheme subs <$> members)
    pure (subs, cls)

  where
    fromMapping subs a = fromJust $ M.lookup a subs
    makeSubs
      = foldrM
          (\var subs -> do
            TyVar new <- freshTyvar
            pure $ M.insert var new subs)
          M.empty

-- | Given the current typeclass context, reduce a list of predicates
-- | to a normal form where no predicate can be derived from the other
-- | predicates
-- |
-- | The resulting elements will retain their respective order
simplify :: AsTypeError e => [Type] -> TC e [Type]
simplify preds = do
  ctxt <- getClassContext
  ctxt' <- traverse standardizeApart ctxt
  go (snd <$> ctxt') [] $ reverse preds
  where
    go ctxt seen [] = pure seen
    go ctxt seen (pred : rest) = do
      res <- entails (seen ++ rest) pred 
      if res
        then go ctxt seen rest
        else go ctxt (pred : seen) rest

-- | Given a typeclass context, does the knowledge base always imply the
-- | goal?
entails
  :: AsTypeError e
  => [Type] -- ^ Knowledge base
  -> Type -- ^ Goal
  -> TC e Bool
entails kb goal = pure False `ifErrorIn` do
  resolvePlaceholder
    False
    S.empty
    (zip (second N.fromList . ctorAndArgs <$> kb) $ repeat Nothing)
    (second N.fromList $ ctorAndArgs goal)
  pure True

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
  :: AsTypeError e
  => Bool -- ^ Defer errors?
  -> Set Identifier -- ^ Type variables bound in the outer context
  -> [(Placeholder, Maybe Expr)] -- ^ Dictionary parameter environment
  -> Expr -- ^ Target expression
  -> TC e ([Placeholder], [Identifier], Expr) -- ^ Deferred placeholders, dictionary variables, resulting expression
resolveAllPlaceholders shouldDeferErrors bound env expr = do
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

    fromDictVar (DictVar _ a) as = a : as
    fromDictVar _ as = as

    go (DictPlaceholder p) = do
      env <- gets snd
      (extra, result) <- lift $ resolvePlaceholder shouldDeferErrors bound (M.toList env) p
      modify $ second (M.union $ M.fromList extra)
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
  :: AsTypeError e
  => Bool -- ^ Defer errors?
  -> Set Identifier -- ^ Type variables bound in the outer context
  -> [(Placeholder, Maybe Expr)] -- ^ Dictionary parameter environment
  -> Placeholder -- ^ The placeholder to construct a dictionary for
  -> TC e ([(Placeholder, Maybe Expr)], Maybe Expr)
resolvePlaceholder shouldDeferErrors bound env goal = do
  ctxt <- getClassContext
  ctxt' <- traverse standardizeApart ctxt
  loop shouldDeferErrors (snd <$> ctxt') bound env goal
  where
    inputTy = toType goal

    isTyVar TyVar{} = True
    isTyVar _ = False

    loop shouldDeferErrors ctxt bound env goal@(con, args)
      | goal `elem` fmap fst env
      , foldMap freeInType args `S.intersection` bound /= S.empty
      = pure ([], Nothing)

      | Just value <- lookup goal env
      , any isTyVar args
      = case value of
          Nothing -> do
            dictVar <- freshDictvar
            pure ([], Just dictVar)
          Just expr -> pure ([], Just expr)

      | otherwise = go goal ctxt
      where
        go _ []
          | shouldDeferErrors = pure ([], Nothing)
          | otherwise = tcError $ _NoSuchInstance # goal

        go goal@(con, args) (entry : entries) =
          case entry of
            TceClass supers className tyVars _
              | let supers' = filter ((== con) . fst) supers
              , ((superName, subs) : _) <-
                  over (mapped._2) (`N.zip` args) supers'
              -> go goal entries `ifErrorIn` do
                  let tyArgs = substitute (Substitution $ N.toList subs) .
                        TyVar <$> tyVars
                  (others, res) <- loop shouldDeferErrors ctxt bound env (className, tyArgs)
                  pure (((className, tyArgs), res) : others, DictSuper superName <$> res)

              | otherwise -> go goal entries

            TceInst modName supers instHead _
              | con == instHead ^. ihClassName
              , all (not . isTyVar) args
              , Right subs <- unify .
                  N.toList $
                  N.zip (toTypeTyVars <$> instHead ^. ihInstArgs) args

              -> go goal entries `ifErrorIn` do
                  let supers' = over (mapped._2.mapped) (substitute subs . TyVar) supers
                  res <- traverse (loop shouldDeferErrors ctxt bound env) supers'
                  pure
                    ( join $ fst <$> res
                    , do
                      res' <- sequence (snd <$> res)
                      let args' = ctorAndArgs <$> args :: NonEmpty (Identifier, [Type])
                      pure $ foldl' App (DictInst (Just modName) con $ fst <$> args') res'
                    )

              | otherwise -> go goal entries
