module Lambda.Core.AST.Definitions where

import           Data.List.NonEmpty         (NonEmpty)
import           Data.Set                   (Set)

import           Lambda.Core.AST.Binding
import           Lambda.Core.AST.Expr
import           Lambda.Core.AST.Identifier
import           Lambda.Core.AST.Types

data ProdDecl
  = ProdDecl
  { prodName     :: Identifier
  , prodArgTypes :: [Type]
  }

data Definition
  -- | ADT Definition: type constructor, type variables, constructor definitions
  = Data Identifier [Identifier] (NonEmpty ProdDecl)
  -- | Type signature: function name, type
  | TypeSignature Identifier TypeScheme
  -- | Function definition
  | Function (Binding Expr)
  -- | Class definition: constraints, class name, type variables, class members
  | Class (Set Type) Identifier [Identifier] [(Identifier, TypeScheme)]
  -- | Classs instance definition: constraints, class name, type arguments, member implementations
  | Instance (Set Type) Identifier [Type] [Binding Expr]
