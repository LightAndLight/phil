{-# language DeriveFunctor #-}
{-# language DeriveTraversable #-}

module Phil.AST.Binding where

import Phil.Core.AST.Identifier

data Binding a
  = VariableBinding Ident a
  | FunctionBinding Ident [Ident] a
  deriving (Eq, Functor, Show, Foldable, Traversable)

bindingName :: Binding a -> Ident
bindingName (VariableBinding name _) = name
bindingName (FunctionBinding name _ _) = name
