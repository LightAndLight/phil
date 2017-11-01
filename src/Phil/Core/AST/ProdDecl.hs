module Phil.Core.AST.ProdDecl where

import Phil.Core.AST.Identifier
import Phil.Core.AST.Types

data ProdDecl
  = ProdDecl
  { prodName :: Ctor
  , prodArgTypes :: [Type]
  } deriving (Eq, Show)
