{-# language DeriveFunctor #-}
{-# language FlexibleContexts #-}
{-# language FunctionalDependencies #-}

module Lambda.Typeclasses
  ( HasTcContext(..)
  , TypeclassEntry(..)
  , checkConstraints
  , equalUpToRenaming
  , elementUpToRenaming
  , getClass
  , getInst
  , getAllSuperclasses
  , getSuperInsts
  ) where

import Control.Lens hiding (Context)
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

import           Lambda.AST.Definitions
import           Lambda.Core.AST.Binding
import           Lambda.Core.AST.Expr
import           Lambda.Core.AST.Identifier
import           Lambda.Core.AST.InstanceHead
import           Lambda.Core.AST.Types
import           Lambda.Core.Kinds
import Lambda.Typecheck.Unification

type Context = [(Identifier, NonEmpty Identifier)]

data TypeclassEntry a
  -- | An instance entry consists of: a context, an instance head, and some function definitions
  = TceInst Context InstanceHead (Map Identifier a)
  -- | A class entry consists of: a context, a constructor applied to one or more type variables,
  -- member type signatures and superclass members
  | TceClass Context Identifier (NonEmpty Identifier) (Map Identifier TypeScheme) [(Identifier, [Identifier])]
  deriving (Eq, Functor, Show)

-- | Look up a class in the context
getClass
  :: [TypeclassEntry a] -- ^ Typeclass context
  -> Identifier -- ^ Class constructor
  -> Maybe (TypeclassEntry a)
getClass [] _ = Nothing
getClass (entry@(TceClass _ className' _ _ _):rest) className 
  | className == className' = Just entry
  | otherwise = getClass rest className
getClass (_:rest) className  = getClass rest className

-- | Look up an instance in the context
getInst
  :: [TypeclassEntry a] -- ^ Typeclass context
  -> Identifier -- ^ Class constructor
  -> NonEmpty Identifier -- ^ Type constructors of the instance arguments
  -> Maybe (TypeclassEntry a)
getInst [] _ _ = Nothing
getInst (entry@(TceInst _ instHead _) : rest) className argCons
  | instHead ^. ihClassName == className
  , fmap fst (instHead ^. ihInstArgs) == argCons
  = Just entry
  | otherwise = getInst rest className argCons
getInst (_:rest) className argCons = getInst rest className argCons

-- | Get all superclasses implied by a class definition, with all type
-- | variables renamed to match those of the original
-- |
-- | Returns Nothing if the class doesn't exist
getAllSuperclasses
  :: [TypeclassEntry a] -- ^ Typeclass context
  -> Identifier
  -> Maybe [TypeclassEntry a]
getAllSuperclasses ctxt className = do
  TceClass supers _ _ _ _ <- getClass ctxt className
  join <$> traverse (go ctxt) supers
  where
    fromMapping :: [(Identifier, Identifier)] -> Identifier -> Identifier
    fromMapping mapping a = fromJust $ lookup a mapping

    rename :: [(Identifier, Identifier)] -> TypeScheme -> TypeScheme
    rename mapping (Forall vars cons ty)
      = let subs = Substitution $ second TyVar <$> mapping
        in Forall
          (S.map (fromMapping mapping) vars)
          (substitute subs <$> cons)
          (substitute subs ty)

    go ctxt (className, tyVars') = do
      TceClass supers constructor tyVars members superMembers <- getClass ctxt className
      let mapping = N.toList $ N.zip tyVars tyVars'
      let supers' = over (mapped._2.mapped) (fromMapping mapping) supers
      let members' = fmap (rename mapping) members

      (TceClass supers' constructor tyVars' members' superMembers :) . join <$> traverse (go ctxt) supers'

-- | Get all the superclass instances implied by an instance
-- |
-- | Returns Nothing if the instance doesn't exist
getSuperInsts
  :: [TypeclassEntry a] -- ^ Typeclass context
  -> Identifier -- ^ Class constructor
  -> NonEmpty Identifier -- ^ Type constructors of the instance arguments
  -> Maybe [TypeclassEntry a]
getSuperInsts ctxt className instArgs = do
  cls@(TceClass context _ tyArgs _ _) <- getClass ctxt className
  let subs = M.fromList . N.toList $ N.zip tyArgs instArgs
  let context' = second (fmap $ fromJust . flip M.lookup subs) <$> context
  join <$> traverse (uncurry go) context'
  where
    go className instArgs = do
      inst <- getInst ctxt className instArgs
      (inst :) <$> getSuperInsts ctxt className instArgs

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
