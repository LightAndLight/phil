{-# language TemplateHaskell #-}
{-# language FlexibleContexts #-}
{-# language FlexibleInstances #-}

module Lambda.Core.Kinds
  ( KindError(..)
  , Kind(..)
  , KindInferenceState(..)
  , HasKindInferenceState(..)
  , HasFreshCount(..)
  , HasKindTable(..)
  , AsKindError(..)
  , applyKindSubs
  , checkDefinitionKinds
  , freshKindVar
  , inferKind
  , initialKindInferenceState
  , runInferKind
  , unifyKinds
  , showKind
  , substituteKind
  , subKindTable
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

data Kind
  = Star
  | KindArrow Kind Kind
  | KindVar Identifier
  | Constraint
  deriving (Eq, Show, Ord)

showKind :: Kind -> String
showKind Star = "*"
showKind Constraint = "Constraint"
showKind (KindArrow k1 k2) = unwords [nested k1, "->", showKind k2]
  where
    nested k@KindArrow{} = "(" ++ showKind k ++ ")"
    nested k = showKind k
showKind (KindVar name) = name

data KindError
  = KNotDefined Identifier
  | KOccurs Identifier
  | KCannotUnify Kind Kind
  | KNotInScope Identifier
  deriving (Eq, Show)

makeClassyPrisms ''KindError

substituteKind :: Map Identifier Kind -> Kind -> Kind
substituteKind subs (KindArrow k1 k2) = KindArrow (substituteKind subs k1) (substituteKind subs k2)
substituteKind subs (KindVar name) = fromMaybe (KindVar name) $ M.lookup name subs
substituteKind subs k = k

-- If we don't instantiate the result of kind inference then we have Kind Polymorphism
instantiate :: Kind -> Kind
instantiate (KindArrow k1 k2) = KindArrow (instantiate k1) (instantiate k2)
instantiate Constraint = Constraint
instantiate _ = Star

-- Apply s1 to s2
applyKindSubs :: Map Identifier Kind -> Map Identifier Kind -> Map Identifier Kind
applyKindSubs s1 = M.union s1 . fmap (substituteKind s1)

subKindTable :: Map Identifier Kind -> Map Identifier Kind -> Map Identifier Kind
subKindTable s1 = fmap (substituteKind s1)

occurs :: Identifier -> Kind -> Bool
occurs name (KindArrow k1 k2) = occurs name k1 || occurs name k2
occurs name (KindVar name') = name == name'
occurs name _ = False

subEquations :: Map Identifier Kind -> [(Kind,Kind)] -> [(Kind,Kind)]
subEquations subs = let f = substituteKind subs in fmap (bimap f f)

unifyKinds :: (AsKindError e, MonadError e m) => [(Kind,Kind)] -> m (Map Identifier Kind)
unifyKinds = unifyKinds'
  where
    unifyKinds' [] = pure M.empty
    unifyKinds' (eq:rest)
      | uncurry (==) eq = unifyKinds' rest
      | otherwise = case eq of
          (KindVar name,k)
            | not $ occurs name k -> do
                let sub = M.singleton name k
                subs' <- unifyKinds' $ subEquations sub rest
                pure $ applyKindSubs subs' sub
            | otherwise -> throwError $ _KOccurs # name
          (k,KindVar name) -> unifyKinds' $ (KindVar name,k):rest
          (KindArrow k1 k2,KindArrow k1' k2') -> unifyKinds' $ [(k1,k1'),(k2,k2')] ++ rest
          (k1,k2) -> throwError $ _KCannotUnify # (k1,k2)

newtype KindInferenceState = KindInferenceState { _kindFreshCount :: Int }

initialKindInferenceState = KindInferenceState 0

class HasKindInferenceState s where
  kindInferenceState :: Lens' s KindInferenceState

class HasFreshCount s where
  freshCount :: Lens' s Int

instance HasFreshCount KindInferenceState where
  freshCount = lens _kindFreshCount (\_ i -> KindInferenceState i)

class HasKindTable s where
  kindTable :: Lens' s (Map Identifier Kind)

instance HasKindTable (Map Identifier Kind) where
  kindTable = lens id (flip const)

freshKindVar :: (HasFreshCount s, MonadState s m) => m Kind
freshKindVar = do
  count <- use freshCount
  freshCount += 1
  pure . KindVar $ "k" ++ show count

inferKind
  :: ( HasFreshCount s
     , MonadState s m
     , HasKindTable r
     , MonadReader r m
     , AsKindError e
     , MonadError e m
     )
  => Type
  -> m (Map Identifier Kind, Kind)
inferKind (TyVar var) = do
  maybeKind <- views kindTable $ M.lookup var
  case maybeKind of
    Just kind -> pure (M.empty,kind)
    Nothing -> throwError $ _KNotInScope # var
inferKind (TyApp con arg) = do
  (s1,conKind) <- inferKind con
  (s2,argKind) <- local (over kindTable $ subKindTable s1) $ inferKind arg
  returnKind <- freshKindVar
  s3 <- unifyKinds [(substituteKind s2 conKind,KindArrow argKind returnKind)]
  pure (applyKindSubs s3 $ applyKindSubs s2 s1,substituteKind s3 returnKind)
inferKind (TyCon tyCon) = case tyCon of
  FunCon -> pure (M.empty,KindArrow Star $ KindArrow Star Star)
  TypeCon con -> do
    maybeKind <- views kindTable $ M.lookup con
    case maybeKind of
      Just kind -> pure (M.empty,kind)
      Nothing -> throwError $ _KNotDefined # con
inferKind (TyPrim _) = pure (M.empty,Star)

runInferKind :: (AsKindError e, MonadError e m) => Type -> Map Identifier Kind -> m (Map Identifier Kind, Kind)
runInferKind ty = flip evalStateT initialKindInferenceState . runReaderT (inferKind ty)

unifyKindsProductArguments
  :: ( HasFreshCount s
     , HasKindTable s
     , MonadState s m
     , AsKindError e
     , MonadError e m
     )
  => [Type]
  -> m (Map Identifier Kind)
unifyKindsProductArguments [] = pure M.empty
unifyKindsProductArguments (ty:tys) = do
  (s1,k1) <- get >>= runReaderT (inferKind ty)
  s2 <- kindTable %= subKindTable s1 >> unifyKindsProductArguments tys
  s3 <- unifyKinds [(substituteKind s2 k1,Star)]
  pure (applyKindSubs s3 $ applyKindSubs s2 s1)

unifyKindsProducts
  :: ( HasFreshCount s
     , HasKindTable s
     , MonadState s m
     , AsKindError e
     , MonadError e m
     )
  => [ProdDecl]
  -> m (Map Identifier Kind)
unifyKindsProducts [] = pure M.empty
unifyKindsProducts (ProdDecl name argTys:prods) = do
  s1 <- unifyKindsProductArguments argTys
  ss <- kindTable %= subKindTable s1 >> unifyKindsProducts prods
  pure $ applyKindSubs ss s1

inferWithTypeVars
  :: ( HasFreshCount s
     , HasKindTable s
     , MonadState s m
     , AsKindError e
     , MonadError e m
     )
  => [Identifier]
  -> NonEmpty ProdDecl
  -> m (Map Identifier Kind,Kind)
inferWithTypeVars [] prods = do
  subs <- unifyKindsProducts $ N.toList prods
  pure (subs, Star)
inferWithTypeVars (tv:tvs) prods = do
  freshVar <- freshKindVar
  (subs,k) <- kindTable %= M.insert tv freshVar >> inferWithTypeVars tvs prods
  pure (subs, KindArrow (substituteKind subs freshVar) k)

checkDefinitionKinds
  :: ( HasKindTable s
     , HasFreshCount s
     , AsKindError e
     , MonadError e m
     )
  => Identifier
  -> [Identifier]
  -> NonEmpty ProdDecl
  -> s
  -> m Kind
checkDefinitionKinds tyCon tyVars prods initialState
  = flip evalStateT initialState $ do
      freshVar <- freshKindVar
      (subs,ty) <- kindTable %= M.insert tyCon freshVar >> inferWithTypeVars tyVars prods
      subs' <- unifyKinds [(freshVar, ty)]
      subs'' <- unifyKinds [(substituteKind subs freshVar, substituteKind subs' freshVar)]
      pure . instantiate $ substituteKind subs'' ty
