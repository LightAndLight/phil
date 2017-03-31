module Lambda.AST.Definitions where

import Data.List.NonEmpty (NonEmpty)
import Lambda.AST.Binding
import Lambda.AST.Expr
import Lambda.Core.AST.Identifier
import Lambda.Core.AST.ProdDecl
import Lambda.Core.AST.Types (Type, TypeScheme)

data Definition
  = Data Identifier [Identifier] (NonEmpty ProdDecl)
  | TypeSignature Identifier TypeScheme
  | Function (Binding Expr)
  | Class [Type] Type [(Identifier, Type)]
  | ValidClass [Type] Identifier [Identifier] [(Identifier, Type)]
  | Instance [Type] Type [Binding Expr]
  | ValidInstance [Type] Identifier [Type] [Binding Expr]
  deriving (Eq, Show)
