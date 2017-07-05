{-# language DeriveFunctor #-}
{-# language DeriveTraversable #-}

module Phil.AST.Binding where

import Phil.Core.AST.Identifier

data Binding a
  = VariableBinding Identifier a
  | FunctionBinding Identifier [Identifier] a
  deriving (Eq, Functor, Show, Foldable, Traversable)

bindingName :: Binding a -> Identifier
bindingName (VariableBinding name _) = name
bindingName (FunctionBinding name _ _) = name
