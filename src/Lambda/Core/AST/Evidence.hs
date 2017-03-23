{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Lambda.Core.AST.Evidence where

import           Lambda.Core.AST.Types

import           Control.Lens
import           Control.Monad.State
import           Data.Map              (Map)
import qualified Data.Set as S
import Data.Set (Set)
import qualified Data.Map              as M

newtype EVar = EVar { getEVar :: Int } deriving (Eq, Ord, Show)

class HasEVarCount s where
  eVarCount :: Lens' s Int

instance HasEVarCount Int where
  eVarCount = lens id (flip const)

freshEVar :: (HasEVarCount s, MonadState s m) => m EVar
freshEVar = do
  count <- use eVarCount
  eVarCount += 1
  pure $ EVar count

data Dictionary
  = Variable EVar
  | Select Dictionary Type
  | Construct Dictionary [Dictionary]
  | Dict Type
  deriving (Eq, Show)

evidenceVariables :: Dictionary -> Set EVar
evidenceVariables (Variable e) = S.singleton e
evidenceVariables (Select dict _) = evidenceVariables dict
evidenceVariables (Construct dict dicts) = evidenceVariables dict `S.union` foldMap evidenceVariables dicts
evidenceVariables _ = S.empty

subDict :: (EVar, Dictionary) -> Dictionary -> Dictionary
subDict (eVar, replacement) dict = case dict of
  Variable eVar'
    | eVar == eVar' -> replacement
    | otherwise -> dict
  Select dict' ty -> Select (subDict (eVar, replacement) dict') ty
  Construct dict' dicts -> Construct (subDict (eVar, replacement) dict') (fmap (subDict (eVar, replacement)) dicts)
  Dict{} -> dict
