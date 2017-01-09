module Test.Lambda.Core.Typecheck (typecheckSpec) where

import           Control.Lens

import           Lambda.Core.AST
import           Lambda.Core.AST.Lens
import           Lambda.Core.Typecheck hiding (unify)
import qualified Lambda.Core.Typecheck as T (unify)

import           Test.Hspec

hasType expr ty = runW expr `shouldSatisfy` unifies ty

unify :: TypeScheme -> TypeScheme -> Either TypeError ()
unify = T.unify

typecheckSpec = describe "Lambda.Core.Typecheck" $ do
  describe "unify" $ do
    let idType = _Forall' ["a"] # _TyFun # (_TyVar # "a", _TyVar # "a")
    it "forall a. a -> a ~ forall b. b -> b" $
      unify idType (_Forall' ["b"] # _TyFun # (_TyVar # "b", _TyVar # "b")) `shouldSatisfy` has _Right
    it "forall a. a -> a ~ forall a b. b -> b" $
      unify idType (_Forall' ["a","b"] # _TyFun # (_TyVar # "b", _TyVar # "b")) `shouldSatisfy` has _Right
    it "forall a. a -> a ~ forall a b. Int -> Int" $
      unify idType (_Forall' ["a","b"] # _TyFun # (_TyPrim # Int, _TyPrim # Int)) `shouldSatisfy` has _Right
    it "forall a. a -> a ~ Int -> Int" $
      unify idType (_Forall' [] # _TyFun # (_TyPrim # Int, _TyPrim # Int)) `shouldSatisfy` has _Right
  describe "w" $ do
    describe "success" $ do
      it "\\x. x : forall a. a -> a" $
        (_Abs' "x" # _Id # "x") `hasType` (_Forall' ["a"] . _TyFun . only (_TyVar # "a", _TyVar # "a"))
      it "\\x. \\y. x : forall a b. a -> b -> a" $
        (_Abs' "x" # _Abs' "y" # _Id # "x")
          `hasType` (_Forall' ["a","b"] . _TyFun . only (_TyVar # "a", _TyFun # (_TyVar # "b", _TyVar # "a")))
      it "rec fix f x = f (fix f) x in rec : forall a. (a -> a) -> a" $
        (_Rec # (_Binding' "fix" # _Abs' "f" # _App # (_Id # "f", _App # (_Id # "fix", _Id # "f")), _Id # "fix"))
          `hasType` (_Forall' ["a"] . _TyFun . only (_TyFun # (_TyVar # "a", _TyVar # "a"), _TyVar # "a"))
    describe "failure" $ do
      it "\\x. x x" $
        runW (_Abs' "x" # _App # (_Id # "x", _Id # "x")) `shouldSatisfy` has (_Left . _OccursError)
