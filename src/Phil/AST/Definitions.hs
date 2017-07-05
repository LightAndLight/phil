module Phil.AST.Definitions
  ( Definition(..)
  ) where

import Control.Lens hiding (Context)
import Data.Foldable
import Data.List.NonEmpty (NonEmpty)

import Phil.AST.Binding
import Phil.AST.Expr
import Phil.Core.AST.Identifier
import Phil.Core.AST.InstanceHead
import Phil.Core.AST.ProdDecl
import Phil.Core.AST.Types

type Context = [(Identifier, NonEmpty Identifier)]

data Definition
  = Data Identifier [Identifier] (NonEmpty ProdDecl)
  | TypeSignature Identifier TypeScheme
  | Function (Binding Expr)
  | Class [Type] Type [(Identifier, Type)]
  | ValidClass Context Identifier (NonEmpty Identifier) [(Identifier, Type)]
  | Instance [Type] Type [Binding Expr]
  | ValidInstance Context InstanceHead [Binding Expr] [Expr]
  deriving (Eq, Show)
