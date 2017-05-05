{-# language DeriveFunctor #-}

module Lambda.Typecheck.TypeclassEntry where

import Control.Lens hiding (Context)
import Control.Monad
import Data.Bifunctor
import Data.List.NonEmpty (NonEmpty)
import Data.Map (Map)
import Data.Maybe

import qualified Data.Map as M
import qualified Data.List.NonEmpty as N
import qualified Data.Set as S

import Lambda.Core.AST.Identifier
import Lambda.Core.AST.InstanceHead
import Lambda.Core.AST.Types
import Lambda.Typecheck.Unification

type Context = [(Identifier, NonEmpty Identifier)]

data TypeclassEntry a
  -- | An instance entry consists of: the module it was defined in,
  -- a context, an instance head, and some function definitions
  = TceInst (NonEmpty Identifier) Context InstanceHead (Map Identifier a)
  -- | A class entry consists of: a context, a constructor applied to one or more type variables,
  -- member type signatures
  | TceClass Context Identifier (NonEmpty Identifier) (Map Identifier TypeScheme)
  deriving (Eq, Functor, Show)

-- | Look up a class in the context
getClass
  :: [TypeclassEntry a] -- ^ Typeclass context
  -> Identifier -- ^ Class constructor
  -> Maybe (TypeclassEntry a)
getClass [] _ = Nothing
getClass (entry@(TceClass _ className' _ _):rest) className 
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
getInst (entry@(TceInst _ _ instHead _) : rest) className argCons
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
  TceClass supers _ _ _ <- getClass ctxt className
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
      TceClass supers constructor tyVars members <- getClass ctxt className
      let mapping = N.toList $ N.zip tyVars tyVars'
      let supers' = over (mapped._2.mapped) (fromMapping mapping) supers
      let members' = fmap (rename mapping) members

      (TceClass supers' constructor tyVars' members' :) . join <$> traverse (go ctxt) supers'

-- | Get all the superclass instances implied by an instance
-- |
-- | Returns Nothing if the instance doesn't exist
getSuperInsts
  :: [TypeclassEntry a] -- ^ Typeclass context
  -> Identifier -- ^ Class constructor
  -> NonEmpty Identifier -- ^ Type constructors of the instance arguments
  -> Maybe [TypeclassEntry a]
getSuperInsts ctxt className instArgs = do
  cls@(TceClass context _ tyArgs _) <- getClass ctxt className
  let subs = M.fromList . N.toList $ N.zip tyArgs instArgs
  let context' = second (fmap $ fromJust . flip M.lookup subs) <$> context
  join <$> traverse (uncurry go) context'
  where
    go className instArgs = do
      inst <- getInst ctxt className instArgs
      (inst :) <$> getSuperInsts ctxt className instArgs
