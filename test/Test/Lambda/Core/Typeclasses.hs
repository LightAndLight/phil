module Test.Lambda.Core.Typeclasses (typeclassesSpec) where

import           Control.Lens                      hiding (elements)
import           Control.Monad.State
import           Data.Maybe
import           Data.Set                          (Set)
import qualified Data.Set                          as S
import           Data.Traversable

import           Lambda.Core.AST.Types
import           Lambda.Typecheck.Unification
import           Lambda.Typecheck.Entailment
import           Lambda.Typeclasses

import           Test.Hspec
import           Test.Hspec.QuickCheck
import           Test.QuickCheck

instance Arbitrary TyCon where
  arbitrary = oneof [pure FunCon, TypeCon <$> arbitrary]

sizedType :: Int -> Gen Type
sizedType 0 = oneof [TyVar <$> listOf1 (elements ['a'..'z']), TyCon <$> arbitrary]
sizedType n = oneof
  [ TyVar <$> listOf1 (elements ['a'..'z'])
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

data ElementUpToRenaming = ElementUpToRenaming Type [Type] deriving (Eq, Show)

instance Arbitrary ElementUpToRenaming where
  arbitrary = do
    ty <- resize 3 arbitrary
    tys <- resize 3 arbitrary
    if isJust (elementUpToRenaming ty tys)
      then pure (ElementUpToRenaming ty tys)
      else arbitrary

typeclassesSpec = describe "Lambda.Core.Typeclasses" $ do
  describe "equalUpToRenaming" $
    describe "forall a : Type, b : Type. Just subs <- equalUpToRenaming a b" $
      prop "subs(b) = subs(a)" $
        \(EqualUpToRenaming a b) ->
          let Just res = equalUpToRenaming a b
          in substitute res b == substitute res a
  describe "elementUpToRenaming" $
    describe "forall a : Type, b : Set Type. Just subs <- elementUpToRenaming a b" $
      prop "subs(a) in subs(b)" $
        \(ElementUpToRenaming a b) ->
          let Just res = elementUpToRenaming a b
          in substitute res a `S.member` S.fromList (fmap (substitute res) b)
  describe "entails" $ do
    let eq a = TyApp (TyCon $ TypeCon "Eq") (TyVar a)
        ord a = TyApp (TyCon $ TypeCon "Ord") (TyVar a)
        num a = TyApp (TyCon $ TypeCon "Num") (TyVar a)
        context =
          [ TceClass [] "Eq" (pure "a") undefined
          , TceClass [eq "b"] "Ord" (pure "b") undefined
          ]
    it "P ||- {}" $
      all (entails [] [ord "c"]) [] `shouldBe` True
    it "given `Eq a` and `Eq b => Ord b`, `Ord c` entails `Eq c`" $
      entails context [ord "c"] (eq "c") `shouldBe` True
    it "given `Eq a` and `Eq b => Ord b`, `Ord c` entails `Ord c`" $
      entails context [ord "c"] (ord "c") `shouldBe` True
    it "given `Eq a` and `Eq b => Ord b`, `Ord c` does not entail `Eq d`" $
      entails context [ord "c"] (eq "d") `shouldBe` False
    it "given `Eq a` and `Eq b => Ord b`, `Ord c` does not entail `Num d`" $
      entails context [ord "c"] (num "d") `shouldBe` False
    let eq = TyApp (TyCon $ TypeCon "Eq")
        ord = TyApp (TyCon $ TypeCon "Ord")
        context' = context ++ [TceInst [] (InstanceHead "Eq" $ pure ("Int", [])) undefined]
        list = TyApp (TyCon $ TypeCon "List")
    it "given `Eq a`, `Eq b => Ord b`, and `Eq Int`, `Eq c` entails `Eq Int`" $
      entails context' [eq $ TyVar "c"] (eq $ TyCtor "Int") `shouldBe` True
    it "given `Eq a`, `Eq b => Ord b`, and `Eq Int`, `Eq c` does not entail `Eq Bool`" $
      entails context' [eq $ TyVar "c"] (eq $ TyCtor "Bool") `shouldBe` False
    it "given `Eq a`, `Eq b => Ord b`, and `Eq Int`, `Eq c` does not entail `Ord Int`" $
      entails context' [eq $ TyVar "c"] (ord $ TyCtor "Int") `shouldBe` False
    let context' = context ++
          [ TceInst [eq $ TyVar "b"] (InstanceHead "Eq" $ pure ("List", ["b"])) undefined
          , TceInst [] (InstanceHead "Eq" $ pure ("Int", [])) undefined
          ]
    it "given `Eq a`, and `Eq b => Eq (List b)`, `Eq c` entails `Eq (List c)`" $
      entails context' [eq $ TyVar "c"] (eq $ TyApp (TyCon $ TypeCon "List") (TyVar "c")) `shouldBe` True
    it "given `Eq a`, `Eq b => Eq (List b)`, and `Eq Int`, `Eq c` entails `Eq (List Int)`" $
      entails context' [eq $ TyVar "c"] (eq $ TyApp (TyCon $ TypeCon "List") (TyCtor "Int")) `shouldBe` True
    let functor a = TyApp (TyCon $ TypeCon "Functor") (TyVar a)
        applicative a = TyApp (TyCon $ TypeCon "Applicative") (TyVar a)
        monad a = TyApp (TyCon $ TypeCon "Monad") (TyVar a)
        context =
          [ TceClass [] "Functor" (pure "a") undefined
          , TceClass [functor "b"] "Applicative" (pure "b") undefined
          , TceClass [applicative "c"] "Monad" (pure "c") undefined
          ]
    it "given `Functor a`, `Functor b => Applicative b` and `Applicative c => Monad c`, `Monad d` entails `Functor d, Applicative d`" $
      all (entails context [monad "d"]) [applicative "d", functor "d"] `shouldBe` True
    it "given `Functor a`, `Functor b => Applicative b` and `Applicative c => Monad c`, `Applicative d` does not entail `Monad d`" $
      entails context [applicative "d"] (monad "d") `shouldBe` False
