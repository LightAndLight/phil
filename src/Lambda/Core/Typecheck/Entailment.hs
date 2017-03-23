{-# LANGUAGE TypeFamilies #-}

module Lambda.Core.Typecheck.Entailment where

import           Control.Applicative
import           Control.Monad.State
import           Data.Map                          (Map)
import qualified Data.Map                          as M
import           Data.Maybe
import           Data.Set                          (Set)
import qualified Data.Set                          as S

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
-- | Super slow
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

standardizeApart :: Set String -> [Statement' a] -> [Statement' a]
standardizeApart seen = flip evalState (seen, M.empty, 0) . traverse standardize
  where
    standardize :: Statement' a -> State (Set String, Map String String, Int) (Statement' a)
    standardize (Apply' a b) = Apply' <$> standardize a <*> traverse standardize b
    standardize (Symbol' a) = pure $ Symbol' a
    standardize (Variable' a) = do
      (_, subs, _) <- get
      case M.lookup a subs of
        Just val -> pure $ Variable' val
        Nothing -> freshVar a

    freshVar :: String -> State (Set String, Map String String, Int) (Statement' a)
    freshVar a = do
      (seen, subs, count) <- get
      let newVar = "v" ++ show count
      if a `S.member` S.insert newVar seen
        then put (seen, subs, count + 1) >> freshVar a
        else put (S.insert newVar seen, M.insert a newVar subs, count + 1) >> pure (Variable' newVar)

vars :: Statement' a -> Set String
vars (Apply' a b) = vars a `S.union` foldMap vars b
vars (Variable' a) = S.singleton a
vars _ = S.empty

entailsForward :: Eq a => [Statement' a] -> Statement' a -> Bool
entailsForward kb q = loop (initCounters kb) kb
  where
    initCounters [] = []
    initCounters (clause : rest) = case clause of
      Implies' (And' ps) q -> (length ps, ps, q) : initCounters rest
      _ -> (0, [], clause) : initCounters rest

    loop toInfer [] = False
    loop toInfer (s : rest)
      = let (toInfer', kb') = updateKnowledge s counters
        in isJust (unify [(q, s)]) || loop counters' (kb' ++ rest)

    updateKnowledge s [] = ([], [])
    updateKnowledge s ((ps, q) : rest) = case unifyWith s ps of
      Nothing -> first ((ps, q) :) $ updateKnowledge s rest
      Just (sub, ps')
        | null ps' -> second (substitute sub q :) $ updateKnowledge s rest
        | otherwise -> first ((ps, substitute sub q) :) updateKnowledge s rest

    unify

a = Apply'
s = Symbol'
v = Variable'
i = Implies'

test = entailsForward
  [ i (And' [s "American" `a` [v "x"], s "Weapon" `a` [v "y"], s "Sells" `a` [v "x", v "y", v "z"], s "Hostile" `a` [v "z"]]) (s "Criminal" `a` [v "x"])
  , s "Owns" `a` [s "Nono", s "M1"]
  , s "Missle" `a` [s "M1"]
  , i (And' [s "Owns" `a` [s "Nono", v "x"], s "Missle" `a` [v "x"]]) (s "Sells" `a` [s "West", v "x", s "Nono"])
  , i (s "Missle" `a` [v "x"]) (s "Weapon" `a` [v "x"])
  , i (s "Enemy" `a` [v "x", s "America"]) (s "Hostile" `a` [v "x"])
  , s "American" `a` [s "West"]
  , s "Enemy" `a` [s "Nono", s "America"]
  ] (Apply' (Symbol' "Criminal") [Symbol' "West"])
