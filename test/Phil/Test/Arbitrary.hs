module Phil.Test.Arbitrary where

import Data.Text (pack)

import           Phil.Core.AST.Identifier
import           Phil.Core.AST.Types
import           Test.QuickCheck

instance Arbitrary Type where
  arbitrary = resize 5 $ sized sizedType

instance Arbitrary Ctor where
  arbitrary = Ctor . pack <$> arbitrary

instance Arbitrary Ident where
  arbitrary = Ident . pack <$> arbitrary

instance Arbitrary TyCon where
  arbitrary = oneof [ pure FunCon, TypeCon <$> arbitrary ]

sizedType :: Int -> Gen Type
sizedType n
  | n < 0 = error "No tree of size zero"
  | n == 0 = oneof [ TyCon <$> arbitrary, TyVar <$> arbitrary ]
  | otherwise
      = oneof
          [ TyFun <$> sizedType (n - 1) <*> sizedType (n - 1)
          ]

newtype Identifier = Identifier String
  deriving (Eq, Show)

instance Arbitrary Identifier where
  arbitrary = Identifier . getNonEmpty <$> arbitrary
