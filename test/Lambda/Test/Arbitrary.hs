module Lambda.Test.Arbitrary where

import Test.QuickCheck
import Lambda hiding (Identifier)

instance Arbitrary Prim where
  arbitrary = elements [Int,String,Char,Bool]

instance Arbitrary Type where
  arbitrary = resize 5 $ sized sizedType

sizedType :: Int -> Gen Type
sizedType n
  | n < 0 = error "No tree of size zero"
  | n == 0 = PrimType <$> arbitrary
  | otherwise
      = oneof 
          [ FunType <$> sizedType (n - 1) <*> sizedType (n - 1)
          ]

newtype Identifier = Identifier String
  deriving (Eq, Show)

instance Arbitrary Identifier where
  arbitrary = Identifier . getNonEmpty <$> arbitrary

