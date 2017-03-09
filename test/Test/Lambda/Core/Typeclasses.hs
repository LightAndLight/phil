module Test.Lambda.Core.Typeclasses (typeclassesSpec) where

import           Data.Maybe
import           Data.Set                           (Set)
import qualified Data.Set                           as S

import           Lambda.Core.AST.Types
import           Lambda.Core.Typecheck.Substitution
import           Lambda.Core.Typeclasses

import           Test.Hspec
import           Test.Hspec.QuickCheck
import           Test.QuickCheck

instance Arbitrary Prim where
  arbitrary = elements [Int, String, Char, Bool]

instance Arbitrary TyCon where
  arbitrary = oneof [pure FunCon, TypeCon <$> arbitrary]

sizedType :: Int -> Gen Type
sizedType 0 = oneof [TyPrim <$> arbitrary, TyVar <$> listOf1 (elements ['a'..'z']), TyCon <$> arbitrary]
sizedType n = oneof
  [ TyPrim <$> arbitrary
  , TyVar <$> listOf1 (elements ['a'..'z'])
  , TyCon <$> arbitrary
  , TyApp <$> sizedType (n-1) <*> sizedType (n-1)
  ]

instance Arbitrary Type where
  arbitrary = sized sizedType

data EqualUpToRenaming = EqualUpToRenaming Type Type deriving (Eq, Show)

instance Arbitrary EqualUpToRenaming where
  arbitrary = do
    ty <- arbitrary
    ty' <- arbitrary
    if isJust (equalUpToRenaming ty ty')
      then pure (EqualUpToRenaming ty ty')
      else arbitrary

data ElementUpToRenaming = ElementUpToRenaming Type (Set Type) deriving (Eq, Show)

instance Arbitrary ElementUpToRenaming where
  arbitrary = do
    ty <- resize 3 arbitrary
    tys <- resize 3 arbitrary
    if isJust (elementUpToRenaming ty tys)
      then pure (ElementUpToRenaming ty tys)
      else arbitrary

data SubsetUpToRenaming = SubsetUpToRenaming (Set Type) (Set Type) deriving (Eq, Show)

instance Arbitrary SubsetUpToRenaming where
  arbitrary = do
    tys <- resize 3 arbitrary
    tys' <- resize 3 arbitrary
    if isJust (subsetUpToRenaming tys tys')
      then pure (SubsetUpToRenaming tys tys')
      else arbitrary

typeclassesSpec = describe "Lambda.Core.Typeclasses" $ do
  describe "equalUpToRenaming" $
    describe "forall a : Type, b : Type. Just subs <- equalUpToRenaming a b" $
      prop "subs(b) = a, subs(a) = a" $
        \(EqualUpToRenaming a b) ->
          let res = fmap TyVar <$> equalUpToRenaming a b
          in substitute (fromJust res) b == a && substitute (fromJust res) a == a
  describe "elementUpToRenaming" $
    describe "forall a : Type, b : Set Type. Just subs <- elementUpToRenaming a b" $
      prop "a in subs(b), subs(a) = a" $
        \(ElementUpToRenaming a b) ->
          let res = fmap TyVar <$> elementUpToRenaming a b
          in a `S.member` S.map (substitute $ fromJust res) b && substitute (fromJust res) a == a
  describe "subsetUpToRenaming" $
    describe "forall a : Set Type, b : Set Type. Just subs <- subsetUpToRenaming a b" $
      prop "a subset subs(b), subs(a) = a" $
        \(SubsetUpToRenaming a b) ->
          let res = fmap TyVar <$> subsetUpToRenaming a b
          in a `S.isSubsetOf` S.map (substitute $ fromJust res) b && S.map (substitute $ fromJust res) a == a
  describe "entails" $ do
    let eq a = TyApp (TyCon $ TypeCon "Eq") (TyVar a)
        ord a = TyApp (TyCon $ TypeCon "Ord") (TyVar a)
        num a = TyApp (TyCon $ TypeCon "Num") (TyVar a)
        context =
          [ TceClass S.empty (eq "a")
          , TceClass (S.fromList [eq "b"]) (ord "b")
          ]
    it "P ||- {}" $
      entails [] (S.fromList [ord "c"]) (S.empty) `shouldBe` True
    it "given `Eq a` and `Eq b => Ord b`, `Ord c` entails `Eq c`" $
      entails context (S.fromList [ord "c"]) (S.fromList [eq "c"]) `shouldBe` True
    it "given `Eq a` and `Eq b => Ord b`, `Ord c` entails `Ord c`" $
      entails context (S.fromList [ord "c"]) (S.fromList [ord "c"]) `shouldBe` True
    it "given `Eq a` and `Eq b => Ord b`, `Ord c` does not entail `Eq d`" $
      entails context (S.fromList [ord "c"]) (S.fromList [eq "d"]) `shouldBe` False
    it "given `Eq a` and `Eq b => Ord b`, `Ord c` does not entail `Num d`" $
      entails context (S.fromList [ord "c"]) (S.fromList [num "d"]) `shouldBe` False
    let eq a = TyApp (TyCon $ TypeCon "Eq") a
        ord a = TyApp (TyCon $ TypeCon "Ord") a
        context' = context ++ [TceInst S.empty (eq $ TyPrim Int)]
    it "given `Eq a`, `Eq b => Ord b`, and `Eq Int`, `Eq c` entails `Eq Int`" $
      entails context' (S.fromList [eq $ TyVar "c"]) (S.fromList [eq $ TyPrim Int]) `shouldBe` True
    it "given `Eq a`, `Eq b => Ord b`, and `Eq Int`, `Eq c` does not entail `Eq Bool`" $
      entails context' (S.fromList [eq $ TyVar "c"]) (S.fromList [eq $ TyPrim Bool]) `shouldBe` False
    it "given `Eq a`, `Eq b => Ord b`, and `Eq Int`, `Eq c` does not entail `Ord Int`" $
      entails context' (S.fromList [eq $ TyVar "c"]) (S.fromList [ord $ TyPrim Int]) `shouldBe` False
    let functor a = TyApp (TyCon $ TypeCon "Functor") (TyVar a)
        applicative a = TyApp (TyCon $ TypeCon "Applicative") (TyVar a)
        monad a = TyApp (TyCon $ TypeCon "Monad") (TyVar a)
        context =
          [ TceClass S.empty (functor "a")
          , TceClass (S.fromList [functor "b"]) (applicative "b")
          , TceClass (S.fromList [applicative "c"]) (monad "c")
          ]
    it "given `Functor a`, `Functor b => Applicative b` and `Applicative c => Monad c`, `Monad d` entails `Functor d, Applicative d`" $
      entails context (S.fromList [monad "d"]) (S.fromList [applicative "d", functor "d"]) `shouldBe` True
    it "given `Functor a`, `Functor b => Applicative b` and `Applicative c => Monad c`, `Applicative d` does not entail `Monad d`" $
      entails context (S.fromList [applicative "d"]) (S.fromList [monad "d"]) `shouldBe` False
