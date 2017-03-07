{-# LANGUAGE TemplateHaskell #-}

module Test.Lambda.Core.Kinds (kindSpec) where

import           Control.Lens
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State
import           Data.Either
import           Data.List.NonEmpty          (NonEmpty (..))
import qualified Data.Map                    as M
import           Data.Traversable

import           Lambda.Core.AST.Definitions
import           Lambda.Core.AST.Identifier
import           Lambda.Core.AST.Types
import           Lambda.Core.Kinds

import           Test.Hspec

data TestState
  = TestState
  { _tsKindTable  :: M.Map Identifier Kind
  , _tsFreshCount :: Int
  }

makeLenses ''TestState

instance HasKindTable TestState where
  kindTable = tsKindTable

instance HasFreshCount TestState where
  freshCount = tsFreshCount

runCheckDefinitionKinds
  :: Identifier
  -> [Identifier]
  -> NonEmpty ProdDecl
  -> Either KindError Kind
runCheckDefinitionKinds name tyVars prods
  = let s = TestState M.empty 0
    in evalStateT (runExceptT (checkDefinitionKinds name tyVars prods)) s s

runInferKindTypeScheme :: [Identifier] -> Type -> Either KindError Kind
runInferKindTypeScheme vars ty = flip evalState (KindInferenceState 0) . runExceptT $ do
  vars' <- for vars $ \var -> (,) var <$> freshKindVar
  fmap snd . flip runReaderT (M.fromList vars') $ inferKind ty

kindSpec = describe "Lambda.Core.Kind" $ do
  describe "checkDefinitionKinds" $ do
    describe "success" $ do
      it "data Unit = Unit : *" $
        runCheckDefinitionKinds "Unit" [] (ProdDecl "Unit" [] :| []) `shouldBe` Right Star
      it "data Identity a = Identity a : * -> *" $
        runCheckDefinitionKinds "Identity" ["a"] (ProdDecl "Identity" [TyVar "a"] :| [])
          `shouldBe` Right (KindArrow Star Star)
      it "data Tuple a b = Tuple a b : * -> * -> *" $
        runCheckDefinitionKinds "Tuple" ["a", "b"] (ProdDecl "Tuple" [TyVar "a", TyVar "b"] :| [])
          `shouldBe` Right (KindArrow Star (KindArrow Star Star))
      it "data Either a b = Left a | Right b : * -> * -> *" $
        runCheckDefinitionKinds "Either" ["a", "b"] (ProdDecl "Left" [TyVar "a"] :| [ProdDecl "Right" [TyVar "b"]])
          `shouldBe` Right (KindArrow Star (KindArrow Star Star))
      it "data List a = Nil | Cons a (List a) : * -> *" $
        runCheckDefinitionKinds "List" ["a"] (ProdDecl "Nil" [] :| [ProdDecl "Cons" [TyVar "a", TyApp (TyCon $ TypeCon "List") (TyVar "a")]])
          `shouldBe` Right (KindArrow Star Star)
      it "data Fix f = Fix (f (Fix f)) : (* -> *) -> *" $
        runCheckDefinitionKinds "Fix" ["f"] (ProdDecl "Fix" [TyApp (TyVar "f") (TyApp (TyCon $ TypeCon "Fix") (TyVar "f"))] :| [])
          `shouldBe` Right (KindArrow (KindArrow Star Star) Star)
      it "data Coproduct f g a = InL (f a) | InR (g a) : (* -> *) -> (* -> *) -> * -> *" $
        runCheckDefinitionKinds "Coproduct" ["f", "g", "a"]
          (ProdDecl "InL" [TyApp (TyVar "f") (TyVar "a")] :| [ProdDecl "InR" [TyApp (TyVar "g") (TyVar "a")]])
          `shouldBe` Right (KindArrow (KindArrow Star Star) (KindArrow (KindArrow Star Star) (KindArrow Star Star)))
    describe "failure" $ do
      it "data Identity a = Identity b" $
        runCheckDefinitionKinds "Identity" ["a"] (ProdDecl "Identity" [TyVar "b"] :| [])
          `shouldSatisfy` isLeft
      it "data Tuple a b = Tuple (a b) a" $
        runCheckDefinitionKinds "Tuple" ["a", "b"] (ProdDecl "Tuple" [TyApp (TyVar "a") (TyVar "b"), TyVar "a"] :| [])
          `shouldSatisfy` isLeft
      it "data List a = Nil | Cons a List" $
        runCheckDefinitionKinds "List" ["a"] (ProdDecl "Nil" [] :| [ProdDecl "Cons" [TyVar "a", TyCon $ TypeCon "List"]])
          `shouldSatisfy` isLeft
      it "data Occurs a b = A (a b) | B (b a)" $
        runCheckDefinitionKinds "Occurs" ["a", "b"] (ProdDecl "A" [TyApp (TyVar "a") (TyVar "b")] :| [ProdDecl "B" [TyApp (TyVar "b") (TyVar "a")]])
          `shouldSatisfy` isLeft
  describe "inferKind" $
    it "forall f a. f a -> f fails" $
      runInferKindTypeScheme ["a", "f"] (TyFun (TyApp (TyVar "f") (TyVar "a")) (TyVar "f"))
        `shouldSatisfy` isLeft
