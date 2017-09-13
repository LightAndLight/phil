{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

module Phil.Typecheck.Unification (
  -- * Constraints
  Constraint,
  -- * Substitutions
  Substitution(..),
  -- * Unification
  UnificationError(..),
  Unify(..),
  unify
) where

import Control.Applicative
import Data.Bifunctor
import Data.Map            (Map)
import Data.Monoid

import qualified Data.Map as M

-- | Assertion that `term = term'`
type Constraint t = (t, t)

-- | Assignments of variables to terms
newtype Substitution t = Substitution { getSubstitution :: Map (Variable t) t }

deriving instance (Show t, Show (Variable t)) => Show (Substitution t)

instance Unify t => Monoid (Substitution t) where
  mempty = Substitution M.empty
  mappend (Substitution s1) s2 = Substitution $ fmap (second $ substitute s2) s1 `M.union` getSubstitution s2

-- | Laws:
-- |
-- | Substitution should be idempotent:
-- | forall s, t, t'. substitute s (substitute s t) = substitute s t
-- |
-- | If a constraint is of the form `variable = term` is "normal":
-- | forall t, t'. isJust (toVariable t) ==> implications (t, t') = [(t, t')]
-- |
-- | The implications of a constraint are all "normal":
-- | forall t, t'. implications (t, t') = join (fmap implications (implications (t, t')))
-- |
-- | Empty implications iff the terms are not unifiable
-- | forall t, t'. implications (t, t') = [] <=> unify [(t, t')] = Left (CannotUnify t t')
-- |
-- | If v occurs in t and t is a variable, then it is a v
-- | forall v, t. occurs v t /\ isJust (toVariable t) ==> v = fromJust (toVariable t)
class Unify term where
  type Variable term

  substitute :: Substitution term -> term -> term
  implications :: (term, term) -> [(term, term)]
  occurs :: Variable term -> term -> Bool
  toVariable :: term -> Maybe (Variable term)

unify :: (Eq term, Unify term) => [(term, term)] -> Either (UnificationError term) (Substitution term)
unify [] = Right mempty
unify ((left, right) : rest)
  | left == right = unify rest
  | otherwise = case toVariable left of
      Just var
        | occurs var right -> Left $ Occurs var right
        | otherwise ->
            let sub = Substitution [(var, right)]
            in (sub <>) <$> unify (bimap (substitute sub) (substitute sub) <$> (left, right) : rest)
      Nothing -> case implications (left, right) of
        [] -> Left $ CannotUnify left right
        impls -> unify (impls ++ rest)

data UnificationError a
  = CannotUnify a a
  | Occurs (Variable a) a

deriving instance (Show a, Show (Variable a)) => Show (UnificationError a)
deriving instance (Eq a, Eq (Variable a)) => Eq (UnificationError a)
