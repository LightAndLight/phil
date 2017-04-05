module Lambda.AST.Definitions
  ( Definition(..)
  ) where

import Control.Lens hiding (Context)
import Data.Foldable
import Data.List.NonEmpty (NonEmpty)

import Lambda.AST.Binding
import Lambda.AST.Expr
import Lambda.Core.AST.Identifier
import Lambda.Core.AST.InstanceHead
import Lambda.Core.AST.ProdDecl
import Lambda.Core.AST.Types

type Context = [(Identifier, NonEmpty Identifier)]

data Definition
  = Data Identifier [Identifier] (NonEmpty ProdDecl)
  | TypeSignature Identifier TypeScheme
  | Function (Binding Expr)
  | Class [Type] Type [(Identifier, Type)]
  | ValidClass Context Identifier (NonEmpty Identifier) [(Identifier, Type)] [(Identifier, [Identifier])]
  | Instance [Type] Type [Binding Expr]
  | ValidInstance Context InstanceHead [InstanceHead] [Binding Expr]
  deriving (Eq, Show)
