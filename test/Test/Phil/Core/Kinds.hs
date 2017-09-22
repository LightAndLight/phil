{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
module Test.Phil.Core.Kinds (kindSpec) where

import Control.Lens
import Control.Monad.Except
import Control.Monad.Fresh
import Control.Monad.Reader
import Control.Monad.State
import Data.Either
import Data.List.NonEmpty (NonEmpty (..))
import Data.Traversable

import qualified Data.Map as M

import Phil.Core.AST.Identifier
import Phil.Core.AST.ProdDecl
import Phil.Core.AST.Types
import Phil.Core.Kinds

import Test.Hspec

data TestState
  = TestState
  { _tsKindTable  :: M.Map (Either Ident Ctor) Kind
  }

makeLenses ''TestState

instance HasKindTable TestState where
  kindTable = tsKindTable

runCheckDefinitionKinds
  :: Ctor
  -> [Ident]
  -> NonEmpty ProdDecl
  -> Either KindError Kind
runCheckDefinitionKinds name tyVars prods =
  let s = TestState M.empty in
    runExcept .
    flip evalStateT s .
    flip runReaderT s .
    runFreshT $
    checkDefinitionKinds name tyVars prods

runInferKindTypeScheme :: [Ident] -> Type -> Either KindError Kind
runInferKindTypeScheme vars ty = runExcept . runFreshT $ do
  vars' <- for vars $ \var -> (,) (Left var :: Either Ident Ctor) <$> freshKindVar
  fmap snd . flip runReaderT (M.fromList vars') $ inferKind ty

kindSpec :: Spec
kindSpec = describe "Phil.Core.Kind" $ do
  describe "checkDefinitionKinds" $ do
    describe "success" $ do

      it "data Unit = Unit : *" $
        runCheckDefinitionKinds
          (Ctor "Unit")
          []
          (ProdDecl (Ctor "Unit") [] :| [])

          `shouldBe`

          Right Star

      it "data Identity a = Identity a : * -> *" $
        runCheckDefinitionKinds
          (Ctor "Identity")
          [Ident "a"]
          (ProdDecl (Ctor "Identity") [TyVar $ Ident "a"] :| [])

          `shouldBe`

          Right (KindArrow Star Star)

      it "data Tuple a b = Tuple a b : * -> * -> *" $
        runCheckDefinitionKinds
          (Ctor "Tuple")
          [Ident "a", Ident "b"]
          (ProdDecl (Ctor "Tuple") [TyVar $ Ident "a", TyVar $ Ident "b"] :| [])

          `shouldBe`

          Right (KindArrow Star (KindArrow Star Star))

      it "data Either a b = Left a | Right b : * -> * -> *" $
        runCheckDefinitionKinds
          (Ctor "Either")
          [Ident "a", Ident "b"]
          (ProdDecl (Ctor "Left") [TyVar $ Ident "a"] :| [ProdDecl (Ctor "Right") [TyVar $ Ident "b"]])

          `shouldBe`

          Right (KindArrow Star (KindArrow Star Star))

      it "data List a = Nil | Cons a (List a) : * -> *" $
        runCheckDefinitionKinds
          (Ctor "List")
          [Ident "a"]
          ( ProdDecl (Ctor "Nil") [] :|
          [ ProdDecl (Ctor "Cons")
            [ TyVar $ Ident "a"
            , TyApp (TyCon $ TypeCon $ Ctor "List") (TyVar $ Ident "a")
            ]
          ])

          `shouldBe`

          Right (KindArrow Star Star)

      it "data Fix f = Fix (f (Fix f)) : (* -> *) -> *" $
        runCheckDefinitionKinds
          (Ctor "Fix")
          [Ident "f"]
          ( ProdDecl (Ctor "Fix")
            [TyApp (TyVar $ Ident "f") (TyApp (TyCon $ TypeCon (Ctor "Fix")) (TyVar $ Ident "f"))] :| [])

          `shouldBe`

          Right (KindArrow (KindArrow Star Star) Star)

      it "data Coproduct f g a = InL (f a) | InR (g a) : (* -> *) -> (* -> *) -> * -> *" $
        runCheckDefinitionKinds
          (Ctor "Coproduct")
          [Ident "f", Ident "g", Ident "a"]
          ( ProdDecl (Ctor "InL") [TyApp (TyVar $ Ident "f") (TyVar $ Ident "a")] :|
          [ ProdDecl (Ctor "InR") [TyApp (TyVar $ Ident "g") (TyVar $ Ident "a")]])

          `shouldBe`

          Right (KindArrow (KindArrow Star Star) (KindArrow (KindArrow Star Star) (KindArrow Star Star)))

    describe "failure" $ do
      it "data Identity a = Identity b" $
        runCheckDefinitionKinds
          (Ctor "Identity")
          [Ident "a"]
          (ProdDecl (Ctor "Identity") [TyVar $ Ident "b"] :| [])

          `shouldSatisfy`

          isLeft

      it "data Tuple a b = Tuple (a b) a" $
        runCheckDefinitionKinds
          (Ctor "Tuple")
          [Ident "a", Ident "b"]
          (ProdDecl (Ctor "Tuple")
            [ TyApp (TyVar $ Ident "a") (TyVar $ Ident "b")
            , TyVar $ Ident "a"
            ] :| [])

        `shouldSatisfy`

        isLeft

      it "data List a = Nil | Cons a List" $
        runCheckDefinitionKinds
          (Ctor "List")
          [Ident "a"]
          ( ProdDecl (Ctor "Nil") [] :|
            [ProdDecl (Ctor "Cons") [TyVar $ Ident "a", TyCon . TypeCon $ Ctor "List"]]
          )

          `shouldSatisfy`

          isLeft

      it "data Occurs a b = A (a b) | B (b a)" $
        runCheckDefinitionKinds
          (Ctor "Occurs")
          [Ident "a", Ident "b"]
          ( ProdDecl (Ctor "A") [TyApp (TyVar $ Ident "a") (TyVar $ Ident "b")] :|
            [ProdDecl (Ctor "B") [TyApp (TyVar $ Ident "b") (TyVar $ Ident "a")]]
          )

          `shouldSatisfy`

          isLeft

  describe "inferKind" $
    it "forall f a. f a -> f fails" $
      runInferKindTypeScheme
        [Ident "a", Ident "f"]
        (TyFun (TyApp (TyVar $ Ident "f") (TyVar $ Ident "a")) (TyVar $ Ident "f"))

        `shouldSatisfy`

        isLeft
