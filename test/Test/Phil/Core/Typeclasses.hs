{-# language OverloadedStrings #-}
module Test.Phil.Core.Typeclasses (typeclassesSpec) where

import Control.Lens hiding (elements)
import Control.Monad.Fresh
import Control.Monad.State
import Data.Maybe
import Data.Set (Set)
import Data.Text (pack)
import Data.Traversable

import qualified Data.Set as S

import Phil.Core.AST.Identifier
import Phil.Core.AST.InstanceHead
import Phil.Core.AST.Types
import Phil.Typecheck.Unification
import Phil.Typecheck.Entailment
import Phil.Typeclasses

import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck

instance Arbitrary TyCon where
  arbitrary = oneof [pure FunCon, TypeCon . Ctor . pack <$> arbitrary]

sizedType :: Int -> Gen Type
sizedType 0 = oneof [TyVar . Ident . pack <$> listOf1 (elements ['a'..'z']), TyCon <$> arbitrary]
sizedType n = oneof
  [ TyVar . Ident . pack <$> listOf1 (elements ['a'..'z'])
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

typeclassesSpec = describe "Phil.Core.Typeclasses" $ do
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

  let eq a = TyApp (TyCon . TypeCon $ Ctor "Eq") (TyVar a)
      ord a = TyApp (TyCon . TypeCon $ Ctor "Ord") (TyVar a)
      num a = TyApp (TyCon . TypeCon $ Ctor "Num") (TyVar a)
      functor a = TyApp (TyCon . TypeCon $ Ctor "Functor") (TyVar a)
      applicative a = TyApp (TyCon . TypeCon $ Ctor "Applicative") (TyVar a)
      monad a = TyApp (TyCon . TypeCon $ Ctor "Monad") (TyVar a)
      monoid a = TyApp (TyCon . TypeCon $ Ctor "Monoid") (TyVar a)

  describe "entails" $ do
    let context =
          [ TceClass [] (Ctor "Eq") (pure $ Ident "a") undefined 
          , TceClass [(Ctor "Eq", pure $ Ident "a")] (Ctor "Ord") (pure $ Ident "a") undefined 
          ]
    it "P ||- {}" $
      all (entails [] [ord $ Ident "c"]) [] `shouldBe` True
    it "given `Eq a` and `Eq a => Ord a`, `Eq c` entails `Eq c`" $
      entails context [eq $ Ident "c"] (eq $ Ident "c") `shouldBe` True
    it "given `Eq a` and `Eq a => Ord a`, `Ord c` entails `Eq c`" $
      entails context [ord $ Ident "c"] (eq $ Ident "c") `shouldBe` True
    it "given `Eq a` and `Eq a => Ord a`, `Ord c` entails `Ord c`" $
      entails context [ord $ Ident "c"] (ord $ Ident "c") `shouldBe` True
    it "given `Eq a` and `Eq a => Ord a`, `[]` does not entail `Eq a`" $
      entails context [] (eq $ Ident "a") `shouldBe` False
    it "given `Eq a` and `Eq a => Ord a`, `Ord c` does not entail `Eq d`" $
      entails context [ord $ Ident "c"] (eq $ Ident "d") `shouldBe` False
    it "given `Eq a` and `Eq a => Ord a`, `Ord c` does not entail `Num d`" $
      entails context [ord $ Ident "c"] (num $ Ident "d") `shouldBe` False
    let eq = TyApp (TyCon . TypeCon $ Ctor "Eq")
        ord = TyApp (TyCon . TypeCon $ Ctor "Ord")
        context' = context ++ [TceInst [] (InstanceHead (Ctor "Eq") $ pure (Ctor "Int", [])) undefined]
        list = TyApp (TyCon . TypeCon $ Ctor "List")
    it "given `Eq a`, `Eq a => Ord a`, and `Eq Int`, `Eq c` entails `Eq Int`" $
      entails context' [eq . TyVar $ Ident "c"] (eq . TyCtor $ Ctor "Int") `shouldBe` True
    it "given `Eq a`, `Eq a => Ord a`, and `Eq Int`, `Eq c` does not entail `Eq Bool`" $
      entails context' [eq . TyVar $ Ident "c"] (eq . TyCtor $ Ctor "Bool") `shouldBe` False
    it "given `Eq a`, `Eq a => Ord a`, and `Eq Int`, `Eq c` does not entail `Ord Int`" $
      entails context' [eq . TyVar $ Ident "c"] (ord . TyCtor $ Ctor "Int") `shouldBe` False
    let context' = context ++
          [ TceInst
              [(Ctor "Eq", pure $ Ident "b")]
              (InstanceHead (Ctor "Eq") $ pure (Ctor "List", [Ident "b"]))
              undefined
          , TceInst [] (InstanceHead (Ctor "Eq") $ pure (Ctor "Int", [])) undefined
          ]
    it "given `Eq a`, and `Eq b => Eq (List b)`, `Eq c` entails `Eq (List c)`" $
      entails
        context'
        [eq . TyVar $ Ident "c"]
        (eq $ TyApp (TyCon . TypeCon $ Ctor "List") (TyVar $ Ident "c"))

        `shouldBe`

        True

    it "given `Eq a`, `Eq b => Eq (List b)`, and `Eq Int`, `Eq c` entails `Eq (List Int)`" $
      entails
        context'
        [eq . TyVar $ Ident "c"]
        (eq $ TyApp (TyCon . TypeCon $ Ctor "List") (TyCtor $ Ctor "Int"))

        `shouldBe`

        True

    let context =
          [ TceClass [] (Ctor "Functor") (pure $ Ident "a") undefined 
          , TceClass
              [(Ctor "Functor", pure $ Ident "b")]
              (Ctor "Applicative")
              (pure $ Ident "b")
              undefined
          , TceClass
              [(Ctor "Applicative", pure $ Ident "c")]
              (Ctor "Monad")
              (pure $ Ident "c")
              undefined
          ]

    it "given `Functor a`, `Functor b => Applicative b` and `Applicative c => Monad c`, `Monad d` entails `Applicative d`" $
      all (entails context [monad $ Ident "d"]) [applicative $ Ident "d"] `shouldBe` True
    it "given `Functor a`, `Functor b => Applicative b` and `Applicative c => Monad c`, `Monad d` entails `Functor d`" $
      entails context [monad $ Ident "d"] (functor $ Ident "d") `shouldBe` True
    it "given `Functor a`, `Functor b => Applicative b` and `Applicative c => Monad c`, `Applicative d` does not entail `Monad d`" $
      entails context [applicative $ Ident "d"] (monad $ Ident "d") `shouldBe` False

    let context =
          [ TceClass [] (Ctor "Monoid") (pure $ Ident "m") undefined
          , TceClass
              [(Ctor "Functor", pure $ Ident "f")]
              (Ctor "Applicative")
              (pure $ Ident "f")
              undefined
          , TceClass [] (Ctor "Functor") (pure $ Ident "f") undefined
          ]

    it "given `Functor f`, `Functor f => Applicative f`, `Applicative d` entails `Applicative d, Functor d`" $
      all (entails context [applicative $ Ident "d"]) [applicative $ Ident "d", functor $ Ident "d"] `shouldBe` True

  describe "simplify" $ do
    let context =
          [ TceClass [] (Ctor "Eq" ) (pure $ Ident "a") undefined 
          ]
    it "(Eq a, Eq a) === Eq a" $
      runIdentity (runFreshT $ simplify context [eq $ Ident "a", eq $ Ident "a"]) `shouldBe` [eq $ Ident "a"]

    let context =
          [ TceClass [] (Ctor "Functor") (pure $ Ident "f") undefined 
          , TceClass [(Ctor "Functor", pure $ Ident "f")] (Ctor "Applicative" ) (pure $ Ident "f") undefined
          , TceClass [(Ctor "Applicative", pure $ Ident "f")] (Ctor "Monad") (pure $ Ident "f") undefined
          ]

    it "Given {} => Functor f and Functor f => Applicative f, (Functor a, Applicative a) === Applicative a" $
      runIdentity
      (runFreshT $ simplify context [functor $ Ident "a", applicative $ Ident "a"])

      `shouldBe`

      [applicative $ Ident "a"]

    it (unwords
      [ "Given {} => Functor f, Functor f => Applicative f and Applicative f => Monad f,"
      , "(Functor a, Applicative a, Functor b, Applicative b, Monad b) === (Applicative a, Monad b)"
      ]) $
      runIdentity
      (runFreshT $
       simplify
         context
         [ functor $ Ident "a"
         , applicative $ Ident "a"
         , functor $ Ident "b"
         , applicative $ Ident "b"
         , monad $ Ident "b"
         ])

      `shouldBe`

      [applicative $ Ident "a", monad $ Ident "b"]
