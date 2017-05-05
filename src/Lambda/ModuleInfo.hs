{-# language TemplateHaskell #-}

module Lambda.ModuleInfo where

import Control.Lens
import Data.List.NonEmpty (NonEmpty)

import Lambda.Core.AST.Identifier
import Lambda.AST.Modules.ModuleName

data ModuleInfo = ModuleInfo { _miModuleName :: ModuleName }

makeClassy ''ModuleInfo
