module Test.Lambda.Core.Typeclasses (typeclassesSpec) where

import           Control.Lens                      hiding (elements)
import           Control.Monad.State
import           Data.Maybe
import           Data.Set                          (Set)
import qualified Data.Set                          as S
import           Data.Traversable

import           Lambda.Core.AST.Evidence
import           Lambda.Core.AST.Types
import           Lambda.Core.Typecheck.Unification
import           qualified Lambda.Core.Typecheck.Entailment as T (entails)
import           Lambda.Core.Typeclasses

import           Test.Hspec
import           Test.Hspec.QuickCheck
import           Test.QuickCheck

instance Arbitrary Prim where
  arbitrary = elements [Int, String, Char, Bool]

instance Arbitrary TyCon where
  arbitrary = oneof [pure FunCon, TypeCon <$> arbitrary]

entails :: [TypeclassEntry] -> [Type] -> Type -> Maybe Dictionary
entails tctxt preds ty =
  let preds' = flip evalState (0 :: Int) $
        for preds $ \p -> (,) <$> (Variable <$> freshEVar) <*> pure p
  in T.entails tctxt preds' ty

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
          [ TceClass [] (eq "a") undefined
          , TceClass [eq "b"] (ord "b") undefined
          ]
    it "P ||- {}" $
      traverse (entails [] [ord "c"]) [] `shouldSatisfy` has _Just
    it "given `Eq a` and `Eq b => Ord b`, `Ord c` entails `Eq c`" $
      entails context [ord "c"] (eq "c") `shouldSatisfy` has _Just
    it "given `Eq a` and `Eq b => Ord b`, `Ord c` entails `Ord c`" $
      entails context [ord "c"] (ord "c") `shouldSatisfy` has _Just
    it "given `Eq a` and `Eq b => Ord b`, `Ord c` does not entail `Eq d`" $
      entails context [ord "c"] (eq "d") `shouldSatisfy` has _Nothing
    it "given `Eq a` and `Eq b => Ord b`, `Ord c` does not entail `Num d`" $
      entails context [ord "c"] (num "d") `shouldSatisfy` has _Nothing
    let eq a = TyApp (TyCon $ TypeCon "Eq") a
        ord a = TyApp (TyCon $ TypeCon "Ord") a
        context' = context ++ [TceInst [] (eq $ TyPrim Int) undefined]
        list a = TyApp (TyCon $ TypeCon "List") a
    it "given `Eq a`, `Eq b => Ord b`, and `Eq Int`, `Eq c` entails `Eq Int`" $
      entails context' [eq $ TyVar "c"] (eq $ TyPrim Int) `shouldSatisfy` has _Just
    it "given `Eq a`, `Eq b => Ord b`, and `Eq Int`, `Eq c` does not entail `Eq Bool`" $
      entails context' [eq $ TyVar "c"] (eq $ TyPrim Bool) `shouldSatisfy` has _Nothing
    it "given `Eq a`, `Eq b => Ord b`, and `Eq Int`, `Eq c` does not entail `Ord Int`" $
      entails context' [eq $ TyVar "c"] (ord $ TyPrim Int) `shouldSatisfy` has _Nothing
    let context' = context ++
          [ TceInst [eq $ TyVar "b"] (eq . list $ TyVar "b") undefined
          , TceInst [] (eq $ TyPrim Int) undefined
          ]
    it "given `Eq a`, and `Eq b => Eq (List b)`, `Eq c` entails `Eq (List c)`" $
      entails context' [eq $ TyVar "c"] (eq $ (TyApp (TyCon $ TypeCon "List")) (TyVar "c")) `shouldSatisfy` has _Just
    it "given `Eq a`, `Eq b => Eq (List b)`, and `Eq Int`, `Eq c` entails `Eq (List Int)`" $
      entails context' [eq $ TyVar "c"] (eq $ (TyApp (TyCon $ TypeCon "List")) (TyPrim Int)) `shouldSatisfy` has _Just
    let functor a = TyApp (TyCon $ TypeCon "Functor") (TyVar a)
        applicative a = TyApp (TyCon $ TypeCon "Applicative") (TyVar a)
        monad a = TyApp (TyCon $ TypeCon "Monad") (TyVar a)
        context =
          [ TceClass [] (functor "a") undefined
          , TceClass [functor "b"] (applicative "b") undefined
          , TceClass [applicative "c"] (monad "c") undefined
          ]
    it "given `Functor a`, `Functor b => Applicative b` and `Applicative c => Monad c`, `Monad d` entails `Functor d, Applicative d`" $
      traverse (entails context [monad "d"]) [applicative "d", functor "d"] `shouldSatisfy` has _Just
    it "given `Functor a`, `Functor b => Applicative b` and `Applicative c => Monad c`, `Applicative d` does not entail `Monad d`" $
      entails context [applicative "d"] (monad "d") `shouldSatisfy` has _Nothing
