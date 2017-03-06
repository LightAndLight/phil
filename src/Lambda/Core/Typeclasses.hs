module Lambda.Core.Typeclasses where

import           Lambda.Core.AST
import           Lambda.Core.Kinds

data Evidence
  = Evidence
  { className     :: Identifier
  , classArgKinds :: [Kind]
  , classImpls    :: [Binding]
  }
