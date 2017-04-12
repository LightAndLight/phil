{-# language DeriveFunctor #-}
{-# language DeriveTraversable #-}
{-# language TemplateHaskell #-}

module Lambda.AST.Modules
  ( Module(..)
  , moduleName
  , moduleExports
  , moduleImports
  , moduleData 
  ) where

import Control.Lens
import Data.List.NonEmpty (NonEmpty)

import Lambda.Core.AST.Identifier
import Lambda.AST.Definitions

data Module a
  = Module
  { _moduleName :: NonEmpty Identifier
  , _moduleExports :: Maybe (NonEmpty Identifier)
  , _moduleImports :: [NonEmpty Identifier]
  , _moduleData :: a
  } deriving (Eq, Foldable, Functor, Show, Traversable)

makeLenses ''Module
