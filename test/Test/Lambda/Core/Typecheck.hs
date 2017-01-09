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
        runW (ast (_Abs' "x" . _Id' "x")) `shouldSatisfy` has (_Right . _Forall' ["t0"] . _TyFun' (_TyVar # "t0") (_TyVar # "t0"))
      it "\\x. \\y. x : forall a b. a -> b -> a" $
        runW (ast (_Abs' "x" . _Abs' "y" . _Id' "x"))
          `shouldSatisfy` has (_Right . _Forall' ["t0","t1"] . _TyFun' (_TyVar # "t0") (_TyFun # (_TyVar # "t1", _TyVar # "t0")))
    describe "failure" $ do
      it "\\x. x x" $
        runW (_Abs' "x" # _App # (_Id # "x", _Id # "x")) `shouldSatisfy` has (_Left . _OccursError)
