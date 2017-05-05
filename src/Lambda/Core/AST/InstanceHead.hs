{-# language TemplateHaskell #-}

module Lambda.Core.AST.InstanceHead where

import Control.Lens
import Data.Char
import Data.Foldable
import Data.List.NonEmpty
import Data.Monoid

import Lambda.Core.AST.Identifier
import Lambda.Core.AST.Types

-- | An instance head has the form: .. => C (T_1 tv_0 tv_1 .. tv_m) (T_2 ..) .. (T_n ..)
-- |
-- | A constructor applied to one or more constructors that are each applied to zero or
-- | more type variables.
data InstanceHead
  = InstanceHead
  { _ihClassName :: Identifier
  , _ihInstArgs :: NonEmpty (Identifier, [Identifier])
  } deriving (Eq, Show)

makeLenses ''InstanceHead

instHeadToType :: InstanceHead -> Type
instHeadToType (InstanceHead className instArgs)
  = foldl' TyApp (TyCtor className) $ toType <$> instArgs
  where
    toType (con, args) = foldl' TyApp (TyCtor con) $ TyVar <$> args

instanceName :: InstanceHead -> String
instanceName (InstanceHead className instArgs)
  = fmap toLower className <> foldMap fst instArgs
