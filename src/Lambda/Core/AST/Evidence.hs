module Lambda.Core.AST.Evidence where

import           Lambda.Core.AST.Types

newtype EVar = EVar { getEVar :: Int } deriving (Eq, Show)

data Evidence
  = Variable EVar
  | Dict Type
  deriving (Eq, Show)
