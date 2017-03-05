{-# LANGUAGE TemplateHaskell #-}

module Test.Lambda.Core.Typecheck (typecheckSpec) where

import           Control.Lens
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State
import           Data.Either
import qualified Data.Map              as M
import           Data.Maybe

import           Lambda.Core.AST
import           Lambda.Core.AST.Lens
import qualified Lambda.Core.Kinds     as K
import           Lambda.Core.Typecheck hiding (special)
import qualified Lambda.Core.Typecheck as T (special)

import           Test.Hspec

newtype TestContext = TestContext { getTestContext :: M.Map Identifier TypeScheme }

instance HasContext TestContext where
  context = lens getTestContext (const TestContext)

special :: TypeScheme -> TypeScheme -> Either TypeError ()
special scheme scheme'
  = flip evalState (TestState K.initialKindInferenceState M.empty 0) .
    flip runReaderT (TestContext M.empty) .
    runExceptT $
    T.special scheme scheme'

hasType :: Expr -> TypeScheme -> Expectation
hasType expr ty = runW expr `shouldSatisfy` (\ty' -> isRight (ty' >>= special ty))

data TestState
  = TestState
  { _tdInferenceState :: K.KindInferenceState
  , _tdKindTable      :: M.Map Identifier K.Kind
  , _tdFreshCount     :: Int
  }

makeLenses ''TestState

instance K.HasFreshCount TestState where
  freshCount = tdInferenceState . K.freshCount

instance K.HasKindTable TestState where
  kindTable = tdKindTable . K.kindTable

instance HasFreshCount TestState where
  freshCount = tdFreshCount

typecheckSpec = describe "Lambda.Core.Typecheck" $ do
  describe "special" $ do
    let idType = _Forall' ["a"] [] # _TyFun # (_TyVar # "a", _TyVar # "a")
    describe "success" $ do
      it "forall a. a -> a is more general than forall b. b -> b" $
        special idType (_Forall' ["b"] [] # _TyFun # (_TyVar # "b", _TyVar # "b")) `shouldSatisfy` has _Right

      it "forall a. a -> a is more general than forall a b. b -> b" $
        special idType (_Forall' ["a","b"] [] # _TyFun # (_TyVar # "b", _TyVar # "b")) `shouldSatisfy` has _Right

      it "forall a. a -> a is more general than forall a b. Int -> Int" $
        special idType (_Forall' ["a","b"] [] # _TyFun # (_TyPrim # Int, _TyPrim # Int)) `shouldSatisfy` has _Right

      it "forall a. a -> a is more general than Int -> Int" $
        special idType (_Forall' [] [] # _TyFun # (_TyPrim # Int, _TyPrim # Int)) `shouldSatisfy` has _Right

      it "forall a. a -> a is more general than forall b c. (b -> c) -> (b -> c)" $
        special idType
          (_Forall' ["b", "c"] []
            # _TyFun
              # ( _TyFun # (_TyVar # "b", _TyVar # "c")
                , _TyFun # (_TyVar # "b", _TyVar # "c"))
          ) `shouldSatisfy` has _Right

    describe "failure" $ do
      it "forall a. a -> a does not unify with forall b c. b -> c" $
        special idType (_Forall' ["b", "c"] [] # _TyFun # (_TyVar # "b", _TyVar # "c")) `shouldSatisfy` has (_Left . _TypeMismatch)

      it "forall a. a -> a does not unify with forall b c d. (b -> c) -> (b -> d)" $
        special idType
          (_Forall' ["b", "c", "d"] []
            # _TyFun
              # ( _TyFun # (_TyVar # "b", _TyVar # "c")
                , _TyFun # (_TyVar # "b", _TyVar # "d"))
          ) `shouldSatisfy` has (_Left . _TypeMismatch)

      it "forall a. a -> a does not unify with forall a b f. f a -> f b" $
        special idType
          (_Forall' ["a", "b", "f"] []
            # _TyFun
              # ( _TyApp # (_TyVar # "f", _TyVar # "a")
                , _TyApp # (_TyVar # "f", _TyVar # "b")
                )
          ) `shouldSatisfy` has (_Left . _TypeMismatch)

      it "Int -> Int is less general than forall a. a -> a" $
        special (_Forall' [] [] # _TyFun # (_TyPrim # Int, _TyPrim # Int)) idType `shouldSatisfy` has (_Left . _TypeMismatch)

  describe "w" $ do
    describe "success" $ do
      it "\\x. x : forall a. a -> a" $
        (_Abs' "x" # _Id # "x") `hasType` (_Forall' ["t0"] [] # _TyFun # (_TyVar # "t0", _TyVar # "t0"))
      it "\\x. \\y. x : forall a b. a -> b -> a" $
        (_Abs' "x" # _Abs' "y" # _Id # "x")
          `hasType` (_Forall' ["t0","t1"] [] # _TyFun # (_TyVar # "t0", _TyFun # (_TyVar # "t1", _TyVar # "t0")))
      it "rec fix f x = f (fix f) x in rec : forall a. (a -> a) -> a" $
        (_Rec # (_Binding' "fix" # _Abs' "f" # _App # (_Id # "f", _App # (_Id # "fix", _Id # "f")), _Id # "fix"))
          `hasType` (_Forall' ["t4"] [] # _TyFun # (_TyFun # (_TyVar # "t4", _TyVar # "t4"), _TyVar # "t4"))
    describe "failure" $ do
      it "\\x. x x" $
        runW (_Abs' "x" # _App # (_Id # "x", _Id # "x")) `shouldSatisfy` has (_Left . _OccursError)
