module Lambda.AST.Modules.ModuleName where

import Data.List.NonEmpty (NonEmpty)

import Lambda.Core.AST.Identifier

type ModuleName = NonEmpty Identifier
