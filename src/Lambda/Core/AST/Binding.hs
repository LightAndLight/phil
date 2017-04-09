{-# LANGUAGE DeriveFunctor #-}

module Lambda.Core.AST.Binding where

import           Lambda.Core.AST.Identifier

data Binding a
  = Binding 
  { bindingName :: Identifier
  , bindingValue :: a
  } deriving (Eq, Show, Functor)
