{-# language DeriveFunctor #-}
{-# language FlexibleContexts #-}
{-# language FunctionalDependencies #-}
{-# language TemplateHaskell #-}

module Lambda.Typeclasses
  ( HasTcContext(..)
  , InstanceHead(..), ihClassName, ihInstArgs, instHeadToType
  , TypeclassEntry(..)
  , checkConstraints
  , equalUpToRenaming
  , elementUpToRenaming
  , getClass
  , getInst
  ) where

import Control.Lens
import Control.Applicative
import Data.Bifunctor
import Control.Monad.Except
import Control.Monad.Fresh
import Control.Monad.Reader
import Data.Traversable
import Data.Monoid
import Control.Monad.State
import Data.Foldable
import qualified Data.Set as S
import Data.Maybe
import qualified Data.Map as M
import Data.Map (Map)
import qualified Data.List.NonEmpty as N
import Data.List.NonEmpty (NonEmpty)
import Data.Set (Set)

import           Lambda.Core.AST.Binding
import           Lambda.Core.AST.Expr
import           Lambda.Core.AST.Identifier
import           Lambda.Core.AST.Types
import           Lambda.Core.Kinds
import Lambda.Typecheck.Unification

-- | An instance head has the form: .. => C (T_1 tv_0 tv_1 .. tv_m) (T_2 ..) .. (T_n ..)
-- |
-- | A constructor applied to one or more constructors that are each applied to zero or
-- | more type variables.
data InstanceHead
  = InstanceHead
  { _ihClassName :: Identifier
  , _ihInstArgs :: NonEmpty (Identifier, [Identifier])
  } deriving (Eq, Show)

instHeadToType :: InstanceHead -> Type
instHeadToType (InstanceHead className instArgs)
  = foldl' TyApp (TyCtor className) $ toType <$> instArgs
  where
    toType (con, args) = foldl' TyApp (TyCtor con) $ TyVar <$> args

makeLenses ''InstanceHead

data TypeclassEntry a
  -- | An instance entry consists of: a context, an instance head, and some function definitions
  = TceInst [Type] InstanceHead (Map Identifier a)
  -- | A class entry consists of: a context, a constructor applied to one or more type variables,
  -- and some function type signatures
  | TceClass [Type] Identifier (NonEmpty Identifier) (Map Identifier TypeScheme)
  deriving (Eq, Functor, Show)

-- | Look up a class in the context
getClass
  :: Identifier -- ^ Class constructor
  -> [TypeclassEntry a] -- ^ Typeclass context
  -> Maybe (TypeclassEntry a)
getClass _ [] = Nothing
getClass className (entry@(TceClass _ className' _ _):rest)
  | className == className' = Just entry
  | otherwise = getClass className rest
getClass className (_:rest) = getClass className rest

-- | Look up an instance in the context by unifying instance heads
getInst
  :: [TypeclassEntry a] -- ^ Typeclass context
  -> Identifier -- ^ Class name
  -> NonEmpty Type -- ^ Instance arguments
  -> Maybe (Substitution Type, TypeclassEntry a)
getInst [] _ _ = Nothing
getInst (entry@(TceInst supers instHead impls) : rest) className instArgs
  | className == instHead ^. ihClassName
  , Right subs <- unify .
  -- Instantiation might be required here
      N.toList $ N.zip (toType <$> instHead ^. ihInstArgs) instArgs
  = pure (subs, entry)
  | otherwise = getInst rest className instArgs
  where
    toType (con, args) = foldl' TyApp (TyCtor con) $ TyVar <$> args
getInst (_ : rest) className instArgs = getInst rest className instArgs

class HasTcContext a s | s -> a where
  tcContext :: Lens' s [TypeclassEntry a]

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

checkConstraints
  :: ( MonadFresh m
     , AsKindError e
     , MonadError e m
     , HasKindTable r
     , MonadReader r m
     ) => [Type] -> m (Substitution Kind)
checkConstraints [] = pure mempty
checkConstraints [con] = do
  (subs, k) <- inferKind con
  either (throwError . review _KUnificationError) (const $ pure subs) $ unify [(k, Constraint)]
checkConstraints (con:rest) = do
  subs <- checkConstraints [con]
  subs' <- local (over kindTable $ subKindTable subs) $ checkConstraints rest
  pure $ subs' <> subs
