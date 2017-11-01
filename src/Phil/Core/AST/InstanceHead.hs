{-# language TemplateHaskell #-}

module Phil.Core.AST.InstanceHead where

import Control.Lens
import Data.Foldable
import Data.List.NonEmpty

import Phil.Core.AST.Identifier
import Phil.Core.AST.Types

-- | An instance head has the form: .. => C (T_1 tv_0 tv_1 .. tv_m) (T_2 ..) .. (T_n ..)
-- |
-- | A constructor applied to one or more constructors that are each applied to zero or
-- | more type variables.
data InstanceHead
  = InstanceHead
  { _ihClassName :: Ctor
  , _ihInstArgs :: NonEmpty (Ctor, [Ident])
  } deriving (Eq, Show)

makeLenses ''InstanceHead

instHeadToType :: InstanceHead -> Type
instHeadToType (InstanceHead className instArgs)
  = foldl' TyApp (TyCtor className) $ toType <$> instArgs
  where
    toType (con, args) = foldl' TyApp (TyCtor con) $ TyVar <$> args


