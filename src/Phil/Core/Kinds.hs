{-# language FlexibleContexts #-}
{-# language FlexibleInstances #-}
{-# language TypeFamilies #-}

module Phil.Core.Kinds
  ( HasKindTable(..)
  , checkDefinitionKinds
  , freshKindVar
  , inferKind
  , lookupKind
  , runInferKind
  , subKindTable
  , module Phil.Core.Kinds.Kind
  , module Phil.Core.Kinds.KindError
  )
  where

import Control.Applicative
import Control.Monad.Fresh
import Control.Lens
import Data.Foldable
import Data.Traversable
import Data.Functor
import Data.Monoid
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

import           Phil.Core.AST.Identifier
import           Phil.Core.AST.Definitions
import           Phil.Core.AST.ProdDecl
import           Phil.Core.AST.Types
import           Phil.Core.Kinds.Kind
import           Phil.Core.Kinds.KindError
import           Phil.Typecheck.Unification


class HasKindTable s where
  kindTable :: Lens' s (Map Identifier Kind)

instance HasKindTable (Map Identifier Kind) where
  kindTable = lens id (flip const)

freshKindVar :: MonadFresh m => m Kind
freshKindVar = KindVar . ("k" ++) <$> fresh

lookupKind :: (AsKindError e, MonadError e m) => Identifier -> Map Identifier Kind -> m Kind
lookupKind name table = case M.lookup name table of
  Nothing -> throwError $ _KNotDefined # name
  Just kind -> pure kind

subKindTable subs = fmap (substitute subs)

inferKind
  :: ( MonadFresh m
     , HasKindTable r
     , MonadReader r m
     , AsKindError e
     , MonadError e m
     )
  => Type
  -> m (Substitution Kind, Kind)
inferKind (TyVar var) = do
  kind <- lookupKind var =<< view kindTable
  pure (mempty, kind)
inferKind (TyApp con arg) = do
  (s1,conKind) <- inferKind con
  (s2,argKind) <- local (over kindTable $ fmap (substitute s1)) $ inferKind arg
  returnKind <- freshKindVar
  case unify [(substitute s2 conKind,KindArrow argKind returnKind)] of
    Right s3 -> pure (s3 <> s2 <> s1, substitute s3 returnKind)
    Left err -> throwError $ _KUnificationError # err
inferKind (TyCon tyCon) = case tyCon of
  FunCon -> pure (mempty, KindArrow Star $ KindArrow Star Star)
  TypeCon con -> do
    kind <- lookupKind con =<< view kindTable
    pure (mempty, kind)

runInferKind :: (AsKindError e, MonadError e m) => Type -> Map Identifier Kind -> m (Substitution Kind, Kind)
runInferKind ty = runFreshT . runReaderT (inferKind ty)

checkDefinitionKinds
  :: ( MonadFresh m
     , HasKindTable r
     , MonadReader r m
     , AsKindError e
     , MonadError e m
     )
  => Identifier
  -> [Identifier]
  -> NonEmpty ProdDecl
  -> m Kind
checkDefinitionKinds tyCon tyVars prods = do
  kinds <- traverse (const freshKindVar) tyVars
  let constructorKind = foldr KindArrow Star kinds
  let update = M.insert tyCon constructorKind . M.union (M.fromList $ zip tyVars kinds)
  subs <- local (over kindTable update) . checkConstructors $ N.toList prods
  pure . instantiateKind $ substitute subs constructorKind
  where
    checkConstructors [] = pure mempty
    checkConstructors (ProdDecl _ argTys:rest) = do
      subs <- checkArgs argTys
      liftA2 (<>) (local (over kindTable $ fmap (substitute subs)) (checkConstructors rest)) (pure subs)

    checkArgs [] = pure mempty
    checkArgs (argTy:rest) = do
      (subs, kind) <- inferKind argTy
      case unify [(kind, Star)] of
        Right subs' -> do
          let subs'' = subs' <> subs
          liftA2 (<>) (local (over kindTable $ fmap (substitute subs'')) (checkArgs rest)) (pure subs'')
        Left err -> throwError $ _KUnificationError # err
