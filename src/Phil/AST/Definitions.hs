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

type Context = [(Ctor, NonEmpty Ident)]

data Definition
  = Data Ctor [Ident] (NonEmpty ProdDecl)
  | TypeSignature Ident TypeScheme
  | Function (Binding Expr)
  | Class [Type] Type [(Ident, Type)]
  | ValidClass Context Ctor (NonEmpty Ident) [(Ident, Type)]
  | Instance [Type] Type [Binding Expr]
  | ValidInstance Context InstanceHead [Binding Expr] [Expr]
  deriving (Eq, Show)
