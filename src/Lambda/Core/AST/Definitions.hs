module Lambda.Core.AST.Definitions where

import           Data.List.NonEmpty         (NonEmpty)
import           Data.Set                   (Set)

import           Lambda.Core.AST.Binding
import           Lambda.Core.AST.Expr
import           Lambda.Core.AST.Identifier
import           Lambda.Core.AST.Types
import           Lambda.Core.AST.ProdDecl

data Definition
  -- | ADT Definition: type constructor, type variables, constructor definitions
  = Data Identifier [Identifier] (NonEmpty ProdDecl)
  -- | Type signature: function name, type
  | TypeSignature Identifier TypeScheme
  -- | Function definition
  | Function (Binding Expr)
  -- | Class definition: constraints, class name, type variables, class members
  | Class [Type] Identifier (NonEmpty Identifier) [(Identifier, Type)]
  -- | Class instance definition: constraints, class name, type arguments, member implementations
  | Instance [Type] Identifier (NonEmpty (Identifier, [Identifier])) [Binding Expr]
  deriving (Eq, Show)
