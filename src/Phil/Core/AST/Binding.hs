{-# LANGUAGE DeriveFunctor #-}
module Phil.Core.AST.Binding where

import Phil.Core.AST.Identifier

data Binding a
  = Binding 
  { bindingName :: Ident
  , bindingValue :: a
  } deriving (Eq, Show, Functor)
