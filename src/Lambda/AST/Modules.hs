{-# language DeriveFunctor #-}
{-# language DeriveTraversable #-}

module Lambda.AST.Modules where

import Data.List.NonEmpty (NonEmpty)

import Lambda.Core.AST.Identifier
import Lambda.AST.Definitions

data Module a
  = Module
  { moduleName :: NonEmpty Identifier
  , moduleExports :: Maybe (NonEmpty Identifier)
  , moduleImports :: [NonEmpty Identifier]
  , moduleDefinitions :: a
  } deriving (Eq, Foldable, Functor, Show, Traversable)
