{-# language TemplateHaskell #-}
{-# language FlexibleContexts #-}

module Lambda.Core.Kinds
  ( KindError(..)
  , Kind(..)
  , KindInferenceState(..)
  , AsKindError(..)
  , checkDefinitionKinds
  , freshKindVar
  , inferKind
  , runInferKind
  , showKind
  )
  where

import Control.Lens
import Data.Foldable
import Data.Traversable
import Data.Functor
import qualified Data.Set as S
import Control.Monad.State
import Control.Monad.Reader
import Data.Maybe
import Control.Monad.Except
import Data.Map (Map)
import Data.Bifunctor
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as N
import qualified Data.Map as M

import           Lambda.Core.AST (Identifier, TyCon (..), Type (..), ProdDecl(..))

data Kind = Star | KindArrow Kind Kind | KindVar Identifier deriving (Eq, Show, Ord)

showKind :: Kind -> String
showKind Star = "*"
showKind (KindArrow k1 k2) = unwords [nested k1, "->", showKind k2]
  where
    nested k@KindArrow{} = "(" ++ showKind k ++ ")"
    nested k = showKind k
showKind (KindVar _) = showKind Star

data KindError
  = KNotDefined Identifier
  | KOccurs Identifier
  | KCannotUnify Kind Kind
  | KNotInScope Identifier
  deriving (Eq, Show)

makeClassyPrisms ''KindError

substitute :: Map Identifier Kind -> Kind -> Kind
substitute subs Star = Star
substitute subs (KindArrow k1 k2) = KindArrow (substitute subs k1) (substitute subs k2)
substitute subs (KindVar name) = fromMaybe (KindVar name) $ M.lookup name subs

-- If we don't instantiate the result of kind inference then we have Kind Polymorphism
instantiate :: Kind -> Kind
instantiate (KindArrow k1 k2) = KindArrow (instantiate k1) (instantiate k2)
instantiate _ = Star

-- Apply s1 to s2
applySubs :: Map Identifier Kind -> Map Identifier Kind -> Map Identifier Kind
applySubs s1 = M.union s1 . fmap (substitute s1)

subKindTable :: Map Identifier Kind -> Map Identifier Kind -> Map Identifier Kind
subKindTable s1 = fmap (substitute s1)

occurs :: Identifier -> Kind -> Bool
occurs name Star = False
occurs name (KindArrow k1 k2) = occurs name k1 || occurs name k2
occurs name (KindVar name') = name == name'

subEquations :: Map Identifier Kind -> [(Kind,Kind)] -> [(Kind,Kind)]
subEquations subs = let f = substitute subs in fmap (bimap f f)

unify :: (AsKindError e, MonadError e m) => [(Kind,Kind)] -> m (Map Identifier Kind)
unify = unify'
  where
    unify' [] = pure M.empty
    unify' (eq:rest)
      | uncurry (==) eq = unify' rest
      | otherwise = case eq of
          (KindVar name,k)
            | not $ occurs name k -> do
                let sub = M.singleton name k
                subs' <- unify' $ subEquations sub rest
                pure $ applySubs subs' sub
            | otherwise -> throwError $ _KOccurs # name
          (k,KindVar name) -> unify' $ (KindVar name,k):rest
          (KindArrow k1 k2,KindArrow k1' k2') -> unify' $ [(k1,k1'),(k2,k2')] ++ rest
          (k1,k2) -> throwError $ _KCannotUnify # (k1,k2)

newtype KindInferenceState = KindInferenceState { _kindFreshCount :: Int }

class HasFreshCount s where
  freshCount :: Lens' s Int

instance HasFreshCount KindInferenceState where
  freshCount = lens _kindFreshCount (\_ i -> KindInferenceState i)

freshKindVar :: (HasFreshCount s, MonadState s m) => m Kind
freshKindVar = do
  count <- use freshCount
  freshCount += 1
  pure . KindVar $ "k" ++ show count

inferKind
  :: ( HasFreshCount s
     , MonadState s m
     , MonadReader (Map Identifier Kind) m
     , AsKindError e
     , MonadError e m
     )
  => Type
  -> m (Map Identifier Kind, Kind)
inferKind (TyVar var) = do
  maybeKind <- asks $ M.lookup var
  case maybeKind of
    Just kind -> pure (M.empty,kind)
    Nothing -> throwError $ _KNotInScope # var
inferKind (TyApp con arg) = do
  (s1,conKind) <- inferKind con
  (s2,argKind) <- local (subKindTable s1) $ inferKind arg
  returnKind <- freshKindVar
  s3 <- unify [(substitute s2 conKind,KindArrow argKind returnKind)]
  pure (applySubs s3 $ applySubs s2 s1,substitute s3 returnKind)
inferKind (TyCon tyCon) = case tyCon of
  FunCon -> pure (M.empty,KindArrow Star $ KindArrow Star Star)
  TypeCon con -> do
    maybeKind <- asks $ M.lookup con
    case maybeKind of
      Just kind -> pure (M.empty,kind)
      Nothing -> throwError $ _KNotDefined # con
inferKind (TyPrim _) = pure (M.empty,Star)

runInferKind :: (AsKindError e, MonadError e m) => Type -> Map Identifier Kind -> m Kind
runInferKind ty = fmap snd . flip evalStateT (KindInferenceState 0) . runReaderT (inferKind ty)

unifyProductArguments
  :: ( HasFreshCount s
     , MonadState s m
     , MonadReader (Map Identifier Kind) m
     , AsKindError e
     , MonadError e m
     )
  => [Type]
  -> m (Map Identifier Kind)
unifyProductArguments [] = pure M.empty
unifyProductArguments (ty:tys) = do
  (s1,k1) <- inferKind ty
  s2 <- local (subKindTable s1) $ unifyProductArguments tys
  s3 <- unify [(substitute s2 k1,Star)]
  pure (applySubs s3 $ applySubs s2 s1)

unifyProducts
  :: ( HasFreshCount s
     , MonadState s m
     , MonadReader (Map Identifier Kind) m
     , AsKindError e
     , MonadError e m
     )
  => [ProdDecl]
  -> m (Map Identifier Kind)
unifyProducts [] = pure M.empty
unifyProducts (ProdDecl name argTys:prods) = do
  s1 <- unifyProductArguments argTys
  ss <- local (subKindTable s1) $ unifyProducts prods
  pure $ applySubs ss s1

inferWithTypeVars
  :: ( MonadReader (Map Identifier Kind) m
     , HasFreshCount s
     , MonadState s m
     , AsKindError e
     , MonadError e m
     )
  => [Identifier]
  -> NonEmpty ProdDecl
  -> m (Map Identifier Kind,Kind)
inferWithTypeVars [] prods = do
  subs <- unifyProducts $ N.toList prods
  pure (subs, Star)
inferWithTypeVars (tv:tvs) prods = do
  freshVar <- freshKindVar
  (subs,k) <- local (M.insert tv freshVar) $ inferWithTypeVars tvs prods
  pure (subs, KindArrow (substitute subs freshVar) k)

checkDefinitionKinds
  :: ( MonadReader (Map Identifier Kind) m
     , AsKindError e
     , MonadError e m
     )
  => Identifier
  -> [Identifier]
  -> NonEmpty ProdDecl
  -> m Kind
checkDefinitionKinds tyCon tyVars prods
  = flip evalStateT (KindInferenceState 0) $ do
      freshVar <- freshKindVar
      (subs,ty) <- local (M.insert tyCon freshVar) $ inferWithTypeVars tyVars prods
      subs' <- unify [(freshVar, ty)]
      subs'' <- unify [(substitute subs freshVar, substitute subs' freshVar)]
      pure . instantiate $ substitute subs'' ty
