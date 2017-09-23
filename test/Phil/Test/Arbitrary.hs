module Phil.Test.Arbitrary where

import           Phil.Core.AST hiding (Identifier)
import           Test.QuickCheck

instance Arbitrary Prim where
  arbitrary = elements [Int,String,Char,Bool]

instance Arbitrary Type where
  arbitrary = resize 5 $ sized sizedType

sizedType :: Int -> Gen Type
sizedType n
  | n < 0 = error "No tree of size zero"
  | n == 0 = TyPrim <$> arbitrary
  | otherwise
      = oneof
          [ TyFun <$> sizedType (n - 1) <*> sizedType (n - 1)
          ]

newtype Identifier = Identifier String
  deriving (Eq, Show)

instance Arbitrary Identifier where
  arbitrary = Identifier . getNonEmpty <$> arbitrary