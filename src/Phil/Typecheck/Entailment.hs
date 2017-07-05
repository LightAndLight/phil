{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

module Phil.Typecheck.Entailment
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

import Phil.AST
import Phil.AST.Expr
import           Phil.Core.AST.Identifier
import           Phil.Core.AST.InstanceHead
import           Phil.Core.AST.Types
import           Phil.Sugar
import           Phil.Typecheck.TypeError
import           Phil.Typecheck.Unification
import           Phil.Typeclasses

-- | Rename all the type variables in a class / instance declaration to fresh
-- | and return the substitution that was created
standardizeApart
  :: MonadFresh m
  => TypeclassEntry a
  -> m (Map Identifier Identifier, TypeclassEntry a)
standardizeApart entry = case entry of
  TceInst supers instHead impls -> do
    let frees = foldr S.insert S.empty . fold $ snd <$> (instHead ^. ihInstArgs)
    subs <- makeSubs frees
    let inst = TceInst
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
          (\var subs -> M.insert var <$> (("t" ++) <$> fresh) <*> pure subs)
          M.empty

-- | Reduce a list of predicates to a normal form where no predicate
-- | can be derived from the other predicates
-- |
-- | The resulting elements will retain their respective order
simplify
  :: MonadFresh m
  => [TypeclassEntry a] -- ^ Typeclass context
  -> [Type] -- ^ Predicates
  -> m [Type]
simplify ctxt preds = do
  ctxt' <- traverse standardizeApart ctxt
  pure . go (snd <$> ctxt') [] $ reverse preds
  where
    go ctxt seen [] = seen
    go ctxt seen (pred : rest)
      | entails ctxt (seen ++ rest) pred 
      = go ctxt seen rest
      | otherwise = go ctxt (pred : seen) rest

-- | Given a typeclass context, does the knowledge base always imply the
-- | goal?
entails
  :: [TypeclassEntry a] -- ^ Typeclass context
  -> [Type] -- ^ Knowledge base
  -> Type -- ^ Goal
  -> Bool
entails ctxt kb goal
  = let res = runExcept . runFreshT $ 
          resolvePlaceholder
            False
            ctxt
            S.empty
            (zip (second N.fromList . ctorAndArgs <$> kb) $ repeat Nothing)
            (second N.fromList $ ctorAndArgs goal)
    in case (res :: Either TypeError ([(Placeholder, Maybe Expr)], Maybe Expr)) of
      Left _ -> False
      Right _ -> True

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
      (extra, result) <- resolvePlaceholder shouldDeferErrors ctxt bound (M.toList env) p
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
  :: ( MonadFresh m
     , AsTypeError e
     , MonadError e m
     )
  => Bool -- ^ Defer errors?
  -> [TypeclassEntry a] -- ^ Typeclass environment
  -> Set Identifier -- ^ Type variables bound in the outer context
  -> [(Placeholder, Maybe Expr)] -- ^ Dictionary parameter environment
  -> Placeholder -- ^ The placeholder to construct a dictionary for
  -> m ([(Placeholder, Maybe Expr)], Maybe Expr)
resolvePlaceholder shouldDeferErrors ctxt bound env goal = do
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
            dictVar <- DictVar . ("dict" ++) <$> fresh
            pure ([], Just dictVar)
          Just expr -> pure ([], Just expr)

      | otherwise = go goal ctxt
      where
        go _ []
          | shouldDeferErrors = pure ([], Nothing)
          | otherwise = throwError $ _NoSuchInstance # goal

        go goal@(con, args) (entry : entries) =
          case entry of
            TceClass supers className tyVars _
              | let supers' = filter ((== con) . fst) supers
              , ((superName, subs) : _) <-
                  over (mapped._2) (`N.zip` args) supers'

              -> flip catchError (const $ go goal entries) $ do
                  let tyArgs = substitute (Substitution $ N.toList subs) .
                        TyVar <$> tyVars
                  (others, res) <- loop shouldDeferErrors ctxt bound env (className, tyArgs)
                  pure (((className, tyArgs), res) : others, DictSuper superName <$> res)

              | otherwise -> go goal entries

            TceInst supers instHead _
              | con == instHead ^. ihClassName
              , all (not . isTyVar) args
              , Right subs <- unify .
                  N.toList $
                  N.zip (toTypeTyVars <$> instHead ^. ihInstArgs) args

              -> flip catchError (const $ go goal entries) $ do
                  let supers' = over (mapped._2.mapped) (substitute subs . TyVar) supers
                  res <- traverse (loop shouldDeferErrors ctxt bound env) supers'
                  pure
                    ( join $ fst <$> res
                    , do
                      res' <- sequence (snd <$> res)
                      let args' = ctorAndArgs <$> args :: NonEmpty (Identifier, [Type])
                      pure $ foldl' App (DictInst con $ fst <$> args') res'
                    )

              | otherwise -> go goal entries
