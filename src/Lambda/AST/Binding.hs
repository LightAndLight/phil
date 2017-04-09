{-# language DeriveFunctor #-}
{-# language DeriveTraversable #-}

module Lambda.AST.Binding where

import Lambda.Core.AST.Identifier

data Binding a
  = VariableBinding Identifier a
  | FunctionBinding Identifier [Identifier] a
  deriving (Eq, Functor, Show, Foldable, Traversable)

bindingName :: Binding a -> Identifier
bindingName (VariableBinding name _) = name
bindingName (FunctionBinding name _ _) = name
