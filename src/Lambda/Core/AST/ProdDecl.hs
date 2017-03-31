module Lambda.Core.AST.ProdDecl where

import Lambda.Core.AST.Identifier
import Lambda.Core.AST.Types

data ProdDecl
  = ProdDecl
  { prodName     :: Identifier
  , prodArgTypes :: [Type]
  } deriving (Eq, Show)
