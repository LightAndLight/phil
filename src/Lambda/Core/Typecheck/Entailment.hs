{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

module Lambda.Core.Typecheck.Entailment where

import           Data.Monoid
import           Data.List
import           Data.Traversable
import           Control.Applicative
import           Control.Monad.State
import           Data.Bifunctor
import           Data.Either
import           Data.Map (Map)
import           Data.Maybe
import           Data.Set (Set)

import qualified Data.Map as M
import qualified Data.Set as S

import           Lambda.Core.Typecheck.Unification

data Statement a
  = Or (Statement a) (Statement a)
  | And (Statement a) (Statement a)
  | Implies (Statement a) (Statement a)
  | Not (Statement a)
  | Literal a
  deriving (Eq, Show, Ord)

bracketed (Literal a) = show a
bracketed (Not a) = showStatement (Not a)
bracketed st = "(" ++ showStatement st ++ ")"

showStatement :: Show a => Statement a -> String
showStatement (Or a b) = bracketed a ++ " \\/ " ++ bracketed b
showStatement (And a b) = bracketed a ++ " /\\ " ++ bracketed b
showStatement (Implies a b) = bracketed a ++ " => " ++ bracketed b
showStatement (Not a) = "~" ++ bracketed a
showStatement (Literal a) = show a

logNegate :: Statement a -> Statement a
logNegate (Not a) = a
logNegate a = Not a

-- | Negative normal form. Removing implications.
nnf :: Statement a -> Statement a
nnf (Implies a b) = nnf $ Or (Not a) b
nnf (Or a b) = Or (nnf a) (nnf b)
nnf (And a b) = And (nnf a) (nnf b)
nnf (Not a) = Not (nnf a)
nnf a = a

-- | Demorgan's Laws
demorgan :: Statement a -> Statement a
demorgan (Not (Or a b)) = And (demorgan $ Not a) (demorgan $ Not b)
demorgan (Not (And a b)) = Or (demorgan $ Not a) (demorgan $ Not b)
demorgan (Not (Not a)) = demorgan a
demorgan (And a b) = And (demorgan a) (demorgan b)
demorgan (Or a b) = Or (demorgan a) (demorgan b)
demorgan (Implies a b) = Implies (demorgan a) (demorgan b)
demorgan a = a

-- | Distribute `ors` inside `ands`
distOr :: Statement a -> Statement a
distOr (Or a (And b c)) = let a' = distOr a in And (Or a' $ distOr b) (Or a' $ distOr c)
distOr (Or (And a b) c) = let c' = distOr c in And (Or (distOr a) c') (Or (distOr b) c')
distOr (And a b) = And (distOr a) (distOr b)
distOr (Not a) = Not (distOr a)
distOr (Implies a b) = Implies (distOr a) (distOr b)
distOr a = a

-- | Translate a statement to conjunctive normal form
cnf :: Statement a -> Statement a
cnf = distOr . demorgan . nnf

-- | Translate a list of statements into a conjunctive normal form, where
-- | a list represents the conjunction of all its elements
cnfList :: [Statement a] -> [Statement a]
cnfList sts = sts >>= conjAsList . cnf
  where
    conjAsList (And a b) = conjAsList a ++ conjAsList b
    conjAsList a = [a]

-- | If a predicate appears in one statement and its negation in the other,
-- | the statements can be merged and that predicate can be discarded
-- |
-- | The `Ord` constraint is required for easy `Set` operations
resolution :: Ord a => Statement a -> Statement a -> Maybe (Statement a)
resolution as bs
  = let aSet = S.fromList (distAsList as)
        bSet = S.fromList (distAsList bs)

        reducedSet = S.filter (\a -> not $ logNegate a `S.member` bSet) aSet `S.union` S.filter (\b -> not $ logNegate b `S.member` aSet) bSet
    in case S.toList reducedSet of
      [] -> Nothing
      [x] -> Just x
      (x:xs) -> Just $ foldr Or x xs
  where
    distAsList (Or a b) = distAsList a ++ distAsList b
    distAsList a = [a]

-- | Search-based entailment
-- |
-- | Basically tries to find counter-examples by iterating over the truth
-- | table.
-- |
-- | The `Ord` constraint is needed for easy `Set` operations
entailsSearch :: Ord a => [Statement a] -> Statement a -> Bool
entailsSearch knowledge query = go $ cnfList (Not query : knowledge)
  where
    go clauses
      = let resolutions = [resolution c_i c_j | c_i <- clauses, c_j <- clauses]
        in case accumulate resolutions of
          Left a -> a
          Right new
            | S.fromList new `S.isSubsetOf` S.fromList clauses -> False
            | otherwise -> go $ clauses ++ new

    accumulate :: [Maybe (Statement a)] -> Either Bool [Statement a]
    accumulate [] = Left False
    accumulate [x] = case x of
      Nothing -> Left True
      Just r -> Right [r]
    accumulate (x : xs) = case x of
      Nothing -> Left True
      Just r -> (r :) <$> accumulate xs

data Statement' a
  = Apply' (Statement' a) [Statement' a]
  | Implies' (Statement' a) (Statement' a)
  | And' [Statement' a]
  | Symbol' a
  | Variable' String
  deriving (Eq, Show, Ord)

instance Eq a => Unify (Statement' a) where
  type Variable (Statement' a) = String

  substitute sub = go $ getSubstitution sub
    where
      go [] st = st
      go subs st = case st of
        Apply' left right -> Apply' (go subs left) (go subs <$> right)
        Implies' left right -> Implies' (go subs left) (go subs right)
        Variable' var' -> fromMaybe st $ lookup var' subs
        And' as -> And' (go subs <$> as)
        Symbol' a -> Symbol' a

  occurs var (Apply' left right) = occurs var left || any (occurs var) right
  occurs var (Implies' left right) = occurs var left || occurs var right
  occurs var (Variable' var') = var == var'
  occurs var (And' as) = any (occurs var) as
  occurs _ _ = False

  toVariable (Variable' var) = Just var
  toVariable _ = Nothing

  implications (Apply' left right, Apply' left' right')
    = let lImpls = implications (left, left')
          rImpls = implications <$> zip right right'
      in if null lImpls || any null rImpls then [] else lImpls ++ join rImpls
  implications (Implies' left right, Implies' left' right')
    = let lImpls = implications (left, left')
          rImpls = implications (right, right')
      in if null lImpls || null rImpls then [] else lImpls ++ rImpls
  implications (And' as, And' as')
    = let impls = implications <$> zip as as'
      in if any null impls then [] else join impls
  implications (Variable' var, st) = [(Variable' var, st)]
  implications (st, Variable' var) = [(Variable' var, st)]
  implications impl
    | uncurry (==) impl = [impl]
    | otherwise = []

isRenaming :: Statement' a -> Statement' a -> Maybe [(String, String)]
isRenaming (Apply' left right) (Apply' left' right') = do
  lNames <- isRenaming left left'
  rNames <- join <$> traverse (uncurry isRenaming) (zip right right')
  if and $ zipWith (\(from, to) (from', to') -> (from /= from') || (to == to')) lNames rNames
    then Just $ lNames ++ rNames
    else Nothing
isRenaming (Implies' left right) (Implies' left' right') = do
  lNames <- isRenaming left left'
  rNames <- isRenaming right right'
  if and $ zipWith (\(from, to) (from', to') -> (from /= from') || (to == to')) lNames rNames
    then Just $ lNames ++ rNames
    else Nothing
isRenaming (Variable' var) (Variable' var') = Just [(var, var')]
isRenaming _ _ = Nothing

vars :: Statement' a -> Set String
vars (Apply' a b) = vars a `S.union` foldMap vars b
vars (Variable' a) = S.singleton a
vars _ = S.empty

initCounters [] = ([], [])
initCounters (clause : rest) = case clause of
  Implies' (And' ps) q -> first ((ps, q) :) $ initCounters rest
  Implies' p q -> first (([p], q) :) $ initCounters rest
  _ -> second (clause :) $ initCounters rest

-- | Forward Chaining
-- |
-- | Forward chaining is based on the extended modus ponens, which states
-- | that:
-- @
--   (p_1 ^ p_2 ^ ... ^ p_n) => q ,  (p_1 ^ p_2 ^ ... ^ p_n)
--   -------------------------------------------------------
--                             q
-- @
-- | A clause in the form '(p_1 ^ p_2 ^ ... ^ p_n) => q', where 'p_i' and
-- | 'q' are atomic (i.e. are symbols, variables, or some combination of
-- | the two) is known as a horn clause.
-- |
-- | So if we have many horn clauses (unknowns), plus some other atomic
-- | clauses (knowns), forward chaining just repeatedly asks:
-- |
-- | "Is the goal an element of the things that I know?"
-- |
-- | If the answer is yes, then the entailment succeeds.
-- |
-- | If not, it then tries to infer new knowledge by using the generalized
-- | modus ponens. If new knowledge can be inferred, the process repeats.
-- | If no new knowledge can be inferred then the entailment fails.
entailsForward :: (Show a, Eq a) => [Statement' a] -> Statement' a -> Bool
entailsForward kb g
  = let (unknowns, knowns) = initCounters kb
    in loop False [] unknowns knowns
  where
    -- Repeatedly loop over the 'unknowns'
    --
    -- Once we get to the end, check whether we deduced anything new
    loop new seen [] knowns
      -- If nothing new was deduced, then our goal is required to exist
      -- our 'knowns'
      | new = loop False [] seen knowns
      | otherwise = g `elem` knowns
      -- If we did, start again
    loop new seen (unknown : rest) knowns
      -- Attempt to apply the generalized modus ponens
      = case reduce unknown knowns of
          -- If the entire left side has been eliminated, then q is a new
          -- deduction
          ([], q) -> loop True seen rest (q : knowns)
          unknown' -> loop new (unknown' : seen) rest knowns

    -- Attempt to reduce the left side of an unknown
    reduce unknown [] = unknown
    reduce (ps, q) (known : rest) = case ps of
      [] -> ([], q)
      _ -> case firstToUnify ps known of
        Nothing -> reduce (ps, q) rest
        Just (sub, ps') ->
          reduce (substitute sub <$> ps', substitute sub q) rest

    -- Finds the first statement in a list that unifies with a fact,
    -- and returns the unifying substitution along with the list minus the
    -- unifying element
    firstToUnify = go []
      where
        go _ [] fact = Nothing
        go seen (p:ps) fact = case unify [(p, fact)] of
          Left _ -> go (p:seen) ps fact
          Right sub -> Just (sub, seen ++ ps)

-- | Standardizing apart
-- |
-- | Each horn clause in a knowledge base needs to have unique variables.
-- | They will be used to generate substitutions, so if there are common
-- | variables across horn clauses then infinite loops may form
standardizeApart :: Statement' a -> State [String] (Statement' a)
standardizeApart st = flip evalStateT M.empty $ case st of
  Implies' p q -> Implies' <$> withFreshVariables p <*> withFreshVariables q
  _ -> pure st
  where
    withFreshVariables st = case st of
      Apply' a as ->
        Apply' <$> withFreshVariables a <*> traverse withFreshVariables as
      Implies' p q ->
        Implies' <$> withFreshVariables p <*> withFreshVariables q
      And' as -> And' <$> traverse withFreshVariables as
      Symbol' a -> pure $ Symbol' a
      Variable' name -> do
        subs <- get
        case M.lookup name subs of
          Nothing -> do
            new : rest <- lift get
            lift $ put rest
            put $ M.insert name new subs
            pure $ Variable' new
          Just name' -> pure $ Variable' name'


-- | Backwards chaining
-- |
-- | Also based on generalized modus ponens, but starts by assuming the
-- | goal.
-- |
-- | The backwards chaining process for knowledge base and a goal asks:
-- |
-- | "Is there anything in the knowledge base that could entail the goal?"
-- |
-- | If the goal exists in the knowledge base, then the answer is yes.
-- | If there is a horn clause in the knowledge base with the goal on the
-- | right side, then the entailment if and only if each clause on the
-- | left side is also entailed by the knowledge base.
entailsBackward :: (Show a, Eq a) => [Statement' a] -> Statement' a -> Bool
entailsBackward kb g =
  let fresh = ("v" ++) <$> fmap show [0..]
      kb' = flip evalState fresh $
        for kb standardizeApart
  in not . null $ solve kb' mempty [g]
  where
    solve kb sub [] = [sub]
    solve kb sub (goal : rest) = loop kb (substitute sub goal) []
      where
        loop [] goal' answers = answers
        loop (r : kbs) goal' answers =
          case r of
            Implies' p q -> case unify [(q, goal')] of
              Left _ -> loop kbs goal' answers
              Right sub' -> case p of
                And' ps ->
                  solve kb (sub' <> sub) (nub $ ps ++ rest) ++ answers
                _ -> solve kb (sub' <> sub) (nub $ p : rest) ++ answers
            q -> case unify [(q, goal')] of
              Left _ -> loop kbs goal' answers
              Right sub' -> solve kb (sub' <> sub) rest ++ answers

a = Apply'
s = Symbol'
v = Variable'
i = Implies'

kb1 = [ i (And' [s "American" `a` [v "x"], s "Weapon" `a` [v "y"], s "Sells" `a` [v "x", v "y", v "z"], s "Hostile" `a` [v "z"]]) (s "Criminal" `a` [v "x"])
  , s "Owns" `a` [s "Nono", s "M1"]
  , s "Missile" `a` [s "M1"]
  , i (And' [s "Owns" `a` [s "Nono", v "x"], s "Missile" `a` [v "x"]]) (s "Sells" `a` [s "West", v "x", s "Nono"])
  , i (s "Missile" `a` [v "x"]) (s "Weapon" `a` [v "x"])
  , i (s "Enemy" `a` [v "x", s "America"]) (s "Hostile" `a` [v "x"])
  , s "American" `a` [s "West"]
  , s "Enemy" `a` [s "Nono", s "America"]
  ]

test1f = entailsForward kb1 (Apply' (Symbol' "Criminal") [Symbol' "West"])
test1b = entailsBackward kb1 (Apply' (Symbol' "Criminal") [Symbol' "West"])

kb2 = [ i (s "A" `a` [v "x"]) (s "B" `a` [v "x"])
  , i (s "B" `a` [v "y"]) (s "C" `a` [v "y"])
  , s "A" `a` [s "bool"]
  , s "A" `a` [s "int"]
  ]

test2f = entailsForward kb2 (s "C" `a` [v "Y"])
test2b = entailsBackward kb2 (s "C" `a` [v "Y"])

kb3 = [ i (And' [s "A" `a` [v "x"], s "B" `a` [v "x"]]) (s "C" `a` [v "x"])
  , s "A" `a` [s "hello"]
  , s "B" `a` [s "hello"]
  ]
  
test3f = entailsForward kb3 (s "C" `a` [s "hello"])
test3b = entailsBackward kb3 (s "C" `a` [s "hello"])

