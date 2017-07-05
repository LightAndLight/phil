module Phil.Core.AST.Definitions (Definition(..)) where

import           Data.List.NonEmpty         (NonEmpty)
import           Data.Set                   (Set)

import           Phil.Core.AST.Binding
import           Phil.Core.AST.Expr
import           Phil.Core.AST.Identifier
import           Phil.Core.AST.InstanceHead
import           Phil.Core.AST.Types
import           Phil.Core.AST.ProdDecl

type Context = [(Identifier, NonEmpty Identifier)]

data Definition
  -- | ADT Definition: type constructor, type variables, constructor definitions
  = Data Identifier [Identifier] (NonEmpty ProdDecl)
  -- | Type signature: function name, type
  | TypeSignature Identifier TypeScheme
  -- | Function definition
  | Function (Binding Expr)
  -- | Class definition: constraints, class name, type variables, class members, superclass members
  | Class Context Identifier (NonEmpty Identifier) [(Identifier, Type)]
  -- | Class instance definition: constraints, class name, type arguments, 
  -- | member implementations, superclass dictionaries
  | Instance Context InstanceHead [Binding Expr] [Expr]
  deriving (Eq, Show)
