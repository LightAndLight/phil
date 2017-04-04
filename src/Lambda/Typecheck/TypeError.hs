{-# language TemplateHaskell #-}

module Lambda.Typecheck.TypeError where

import Control.Lens
import Data.List.NonEmpty (NonEmpty)
import Data.Set (Set)

import Lambda.Core.AST.Identifier
import Lambda.Core.AST.Types
import Lambda.Core.Kinds
import Lambda.Typecheck.Unification

data TypeError
  = NotInScope [String]
  | PatternArgMismatch Int Int
  | AlreadyDefined Identifier
  | TooManyArguments TypeScheme
  | WrongArity [Type]
  | NotDefined Identifier
  | DuplicateTypeSignatures Identifier
  | KindInferenceError KindError
  | CouldNotDeduce [Type] [Type]
  | NoSuchClass Identifier
  | NoSuchInstance Identifier (NonEmpty Type)
  | NonClassFunction Identifier (NonEmpty Type) Identifier
  | MissingClassFunctions Identifier (NonEmpty Type) (Set Identifier)
  | MissingSuperclassInsts [Type]
  | TypeMismatch TypeScheme TypeScheme
  | TUnificationError (UnificationError Type)
  deriving (Eq, Show)

makeClassyPrisms ''TypeError

instance AsKindError TypeError where
  _KindError = _KindInferenceError . _KindError
