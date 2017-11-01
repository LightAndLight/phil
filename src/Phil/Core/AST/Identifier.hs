{-# language DeriveGeneric #-}
module Phil.Core.AST.Identifier where

import GHC.Generics
import Data.Text (Text)

newtype Ident = Ident { getIdent :: Text }
  deriving (Eq, Ord, Show, Generic)

newtype Ctor = Ctor { getCtor :: Text }
  deriving (Eq, Ord, Show, Generic)
