module Test.Lambda.Core.Typecheck (typecheckSpec) where

import           Control.Lens

import           Lambda.Core.AST
import           Lambda.Core.AST.Lens
import           Lambda.Core.Typecheck

import           Test.Hspec

typecheckSpec = describe "Lambda.Core.Typecheck" $
  describe "w" $ do
    describe "success" $ do
      it "\\x. x : forall a. a -> a" $
        runW (_Abs' "x" # _Id # "x") `shouldSatisfy` has (_Right . _Forall' ["t0"] . _TyFun . only (_TyVar # "t0", _TyVar # "t0"))
      it "\\x. \\y. x : forall a b. a -> b -> a" $
        runW (_Abs' "x" # _Abs' "y" # _Id # "x")
          `shouldSatisfy` has (_Right . _Forall' ["t0","t1"] . _TyFun . only (_TyVar # "t0", _TyFun # (_TyVar # "t1", _TyVar # "t0")))
      it "rec fix f x = f (fix f) x in rec : forall a. (a -> a) -> a" $ do
        runW (_Rec # (_Binding' "fix" # _Abs' "f" # _App # (_Id # "f", _App # (_Id # "fix", _Id # "f")), _Id # "fix"))
          `shouldSatisfy` has (_Right . _Forall' ["t4"] . _TyFun . only (_TyFun # (_TyVar # "t4", _TyVar # "t4"), _TyVar # "t4"))
    describe "failure" $ do
      it "\\x. x x" $
        runW (_Abs' "x" # _App # (_Id # "x", _Id # "x")) `shouldSatisfy` has (_Left . _OccursError)
