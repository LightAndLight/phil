{-# LANGUAGE DeriveFunctor #-}

module Phil.Core.AST.Binding where

import           Phil.Core.AST.Identifier

data Binding a
  = Binding 
  { bindingName :: Identifier
  , bindingValue :: a
  } deriving (Eq, Show, Functor)
