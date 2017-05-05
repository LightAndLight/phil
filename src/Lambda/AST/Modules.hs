{-# language DeriveFunctor #-}
{-# language DeriveTraversable #-}
{-# language TemplateHaskell #-}

module Lambda.AST.Modules
  ( Module(..)
  , toModuleName
  , toModulePath
  , moduleName
  , moduleExports
  , moduleImports
  , moduleData 
  ) where

import Control.Lens hiding ((<.>))
import Data.Foldable
import Data.List
import Data.List.NonEmpty (NonEmpty)
import System.FilePath

import qualified Data.List.NonEmpty as N

import Lambda.Core.AST.Identifier
import Lambda.AST.Definitions
import Lambda.AST.Modules.ModuleName

toModuleName :: ModuleName -> String
toModuleName = fold . intersperse "." . N.toList

toModulePath :: ModuleName -> FilePath
toModulePath = (<.> "lam") . foldr1 (</>)

data Module a
  = Module
  { _moduleName :: ModuleName
  , _moduleExports :: Maybe (NonEmpty Identifier)
  , _moduleImports :: [ModuleName]
  , _moduleData :: a
  } deriving (Eq, Foldable, Functor, Show, Traversable)

makeLenses ''Module
