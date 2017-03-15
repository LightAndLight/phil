{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Lambda.Core.AST.Evidence where

import           Lambda.Core.AST.Types

import           Control.Lens
import           Control.Monad.State
import           Data.Map              (Map)
import qualified Data.Map              as M

newtype EVar = EVar { getEVar :: Int } deriving (Eq, Ord, Show)

class HasEVarCount s where
  eVarCount :: Lens' s Int

freshEVar :: (HasEVarCount s, MonadState s m) => m EVar
freshEVar = do
  count <- use eVarCount
  eVarCount += 1
  pure $ EVar count

data Dictionary
  = Variable EVar
  | Super Dictionary Type
  | Construct Dictionary [Dictionary]
  | Dict Type
  deriving (Eq, Show)

substituteDictionary :: (EVar, Dictionary) -> Dictionary -> Dictionary
substituteDictionary (eVar, replacement) dict = case dict of
  Variable eVar'
    | eVar == eVar' -> replacement
    | otherwise -> dict
  Super dict' ty -> Super (substituteDictionary (eVar, replacement) dict') ty
  Construct dict' dicts -> Construct (substituteDictionary (eVar, replacement) dict') (fmap (substituteDictionary (eVar, replacement)) dicts)
  Dict{} -> dict
