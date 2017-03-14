{-# LANGUAGE TemplateHaskell #-}

module Test.Lambda.Core.Typecheck (typecheckSpec) where

import           Control.Lens
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State
import           Data.Either
import qualified Data.Map                   as M
import           Data.Maybe
import qualified Data.Set                   as S

import           Lambda.Core.AST.Evidence
import           Lambda.Core.AST.Expr
import           Lambda.Core.AST.Identifier
import           Lambda.Core.AST.Lens
import           Lambda.Core.AST.Types
import qualified Lambda.Core.Kinds          as K
import           Lambda.Core.Typecheck      hiding (special)
import qualified Lambda.Core.Typecheck      as T (special)
import           Lambda.Core.Typeclasses

import           Test.Hspec

data TestContexts
  = TestContexts
  { _testContext   :: M.Map Identifier TypeScheme
  , _testTcContext :: [TypeclassEntry]
  }

emptyContexts = TestContexts M.empty []

makeClassy ''TestContexts

instance HasContext TestContexts where
  context = testContexts . testContext

instance HasTcContext TestContexts where
  tcContext = testContexts . testTcContext

data TestState
  = TestState
  { _tdInferenceState :: K.KindInferenceState
  , _tdKindTable      :: M.Map Identifier K.Kind
  , _tdFreshCount     :: Int
  , _tdEVarCount      :: Int
  , _tdTcContext      :: [TypeclassEntry]
  }

initialTestState = TestState K.initialKindInferenceState M.empty 0 0 []

makeLenses ''TestState

instance K.HasFreshCount TestState where
  freshCount = tdInferenceState . K.freshCount

instance K.HasKindTable TestState where
  kindTable = tdKindTable . K.kindTable

instance HasFreshCount TestState where
  freshCount = tdFreshCount

instance HasEVarCount TestState where
  eVarCount = tdEVarCount

instance HasTcContext TestState where
  tcContext = tdTcContext

special :: TestContexts -> TypeScheme -> TypeScheme -> Either TypeError ()
special ctxts scheme scheme'
  = flip evalState initialTestState .
    flip runReaderT ctxts .
    runExceptT $
    T.special scheme scheme'

hasType :: Expr -> TypeScheme -> Expectation
hasType expr ty = snd <$> runW expr `shouldSatisfy` (\ty' -> isRight (ty' >>= special emptyContexts ty))

typeOf :: TestContexts -> TestState -> Expr -> Either TypeError TypeScheme
typeOf ctxt st expr
  = flip runReader ctxt .
    flip evalStateT st .
    runExceptT $ snd <$> w expr

typecheckSpec = describe "Lambda.Core.Typecheck" $ do
  describe "special" $ do
    let idType = _Forall' ["a"] [] # _TyFun # (_TyVar # "a", _TyVar # "a")
    describe "success" $ do
      it "forall a. a -> a is more general than forall b. b -> b" $
        special emptyContexts idType (_Forall' ["b"] [] # _TyFun # (_TyVar # "b", _TyVar # "b")) `shouldSatisfy` has _Right

      it "forall a. a -> a is more general than forall a b. b -> b" $
        special emptyContexts idType (_Forall' ["a","b"] [] # _TyFun # (_TyVar # "b", _TyVar # "b")) `shouldSatisfy` has _Right

      it "forall a. a -> a is more general than forall a b. Int -> Int" $
        special emptyContexts idType (_Forall' ["a","b"] [] # _TyFun # (_TyPrim # Int, _TyPrim # Int)) `shouldSatisfy` has _Right

      it "forall a. a -> a is more general than Int -> Int" $
        special emptyContexts idType (_Forall' [] [] # _TyFun # (_TyPrim # Int, _TyPrim # Int)) `shouldSatisfy` has _Right

      it "forall a. a -> a is more general than forall b c. (b -> c) -> (b -> c)" $
        special emptyContexts idType
          (_Forall' ["b", "c"] []
            # _TyFun
              # ( _TyFun # (_TyVar # "b", _TyVar # "c")
                , _TyFun # (_TyVar # "b", _TyVar # "c"))
          ) `shouldSatisfy` has _Right

    describe "failure" $ do
      it "forall a. a -> a does not unify with forall b c. b -> c" $
        special emptyContexts idType (_Forall' ["b", "c"] [] # _TyFun # (_TyVar # "b", _TyVar # "c")) `shouldSatisfy` has (_Left . _TypeMismatch)

      it "forall a. a -> a does not unify with forall b c d. (b -> c) -> (b -> d)" $
        special emptyContexts idType
          (_Forall' ["b", "c", "d"] []
            # _TyFun
              # ( _TyFun # (_TyVar # "b", _TyVar # "c")
                , _TyFun # (_TyVar # "b", _TyVar # "d"))
          ) `shouldSatisfy` has (_Left . _TypeMismatch)

      it "forall a. a -> a does not unify with forall a b f. f a -> f b" $
        special emptyContexts idType
          (_Forall' ["a", "b", "f"] []
            # _TyFun
              # ( _TyApp # (_TyVar # "f", _TyVar # "a")
                , _TyApp # (_TyVar # "f", _TyVar # "b")
                )
          ) `shouldSatisfy` has (_Left . _TypeMismatch)

      it "Int -> Int is less general than forall a. a -> a" $
        special emptyContexts (_Forall' [] [] # _TyFun # (_TyPrim # Int, _TyPrim # Int)) idType `shouldSatisfy` has (_Left . _TypeMismatch)

  describe "typeclass" $ do
    let constrainedId = _Forall' ["a"] [TyApp (TyCon $ TypeCon "Constraint") (TyVar "a")] # _TyFun # (_TyVar # "a", _TyVar # "a")
        regularId = _Forall' ["a"] [] # _TyFun # (_TyVar # "a", _TyVar # "a")
        intToInt = _Forall' [] [] # _TyFun # (_TyPrim # Int, _TyPrim # Int)

    describe "success" $ do
      let ctxt = emptyContexts
            { _testTcContext =
              [ TceClass S.empty (TyApp (TyCon $ TypeCon "Constraint") (TyVar "b")) undefined
              , TceInst S.empty (TyApp (TyCon $ TypeCon "Constraint") (TyPrim Int)) undefined
              ]
            }
      it "forall a. a -> a [>=] forall a. Constraint a => a -> a" $
        special emptyContexts regularId constrainedId `shouldSatisfy` has _Right
      it "forall a. Constraint a => a -> a not [>=] forall a. a -> a" $
        special emptyContexts constrainedId regularId `shouldSatisfy` has _Left
      it "instance Constraint Int where ... ==> forall a. Constraint a => a -> a [>=] Int -> Int" $
        special ctxt constrainedId intToInt `shouldSatisfy` has _Right

    describe "failure" $ do
      let ctxt = emptyContexts { _testTcContext = [TceClass S.empty (TyApp (TyCon $ TypeCon "Constraint") (TyVar "b")) undefined] }
      it "forall a. Constraint a => a -> a [>=] Int -> Int but there is no instance Constraint Int" $
        special ctxt constrainedId intToInt `shouldSatisfy` has (_Left . _CouldNotDeduce)
      let constrainedId = _Forall'
            ["a"]
            [ TyApp (TyCon $ TypeCon "Constraint") (TyVar "a")
            , TyApp (TyCon $ TypeCon "Other") (TyVar "a")
            ]
            # _TyFun # (_TyVar # "a", _TyVar # "a")
          ctxt = emptyContexts
            { _testTcContext =
              [ TceClass S.empty (TyApp (TyCon $ TypeCon "Constraint") (TyVar "b")) undefined
              , TceInst S.empty (TyApp (TyCon $ TypeCon "Constraint") (TyPrim Int)) undefined
              ]
            }
      it "instance Constraint Int where ... => forall a. (Constraint a, Other a) => a -> a [>=] Int -> Int but there is no class `Other`" $
        special ctxt constrainedId intToInt `shouldSatisfy` has (_Left . _CouldNotDeduce)

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

    describe "typeclasses" $ do
      Test.Hspec.context "class Eq a where eq : a -> a -> Bool where ..." $ do
        let ctxt = emptyContexts
              { _testContext = M.singleton "eq" $
                  _Forall'
                    ["a"]
                    [TyApp (TyCon $ TypeCon "Eq") $ TyVar "a"]
                    # _TyFun # (_TyVar # "a", _TyFun # (_TyVar # "a", _TyPrim # Bool))
              , _testTcContext =
                  [ TceClass S.empty (TyApp (TyCon $ TypeCon "Eq") $ TyVar "a") undefined]
              }
        it "\\x. \\y. eq y x : forall a. Eq a => a -> a -> Bool" $ do
          typeOf ctxt initialTestState (_Abs' "x" # _Abs' "y" # _App # (_App # (_Id # "eq", _Id # "y"), _Id # "x"))
            `shouldBe` (Right $
              Forall
                (S.singleton "t2")
                (S.singleton $ TyApp (TyCon $ TypeCon "Eq") (TyVar "t2"))
                (TyFun (TyVar "t2") $ TyFun (TyVar "t2") (TyPrim Bool)))
        it "\\x. eq x x : forall a. Eq a => a -> Bool" $ do
          typeOf ctxt initialTestState (_Abs' "x" # _App # (_App # (_Id # "eq", _Id # "x"), _Id # "x"))
            `shouldBe` (Right $
              Forall
                (S.singleton "t1")
                (S.singleton $ TyApp (TyCon $ TypeCon "Eq") (TyVar "t1"))
                (TyFun (TyVar "t1") (TyPrim Bool)))
        Test.Hspec.context "and : Bool -> Bool -> Bool" $ do
          let ctxtWithAnd = ctxt & over testContext
                ( M.insert "and" $
                    _Forall'
                      ["a"]
                      []
                      # _TyFun # (_TyPrim # Bool, _TyFun # (_TyPrim # Bool, _TyPrim # Bool))
                )
          it "\\x y. and (eq x x) (eq y y) : forall a a1. (Eq a, Eq a1) => a -> a1 -> Bool" $ do
            let eqxx = _App # (_App # (_Id # "eq", _Id # "x"), _Id # "x")
                eqyy = _App # (_App # (_Id # "eq", _Id # "y"), _Id # "y")
            typeOf ctxtWithAnd initialTestState (_Abs' "x" # _Abs' "y" # _App # (_App # (_Id # "and", eqxx), eqyy))
              `shouldBe` (Right $
                Forall
                  (S.fromList ["t3", "t7"])
                  (S.fromList
                    [ TyApp (TyCon $ TypeCon "Eq") (TyVar "t3")
                    , TyApp (TyCon $ TypeCon "Eq") (TyVar "t7")
                    ]
                  )
                  (TyFun (TyVar "t3") $ TyFun (TyVar "t7") $ TyPrim Bool))
          Test.Hspec.context "class Gt a where gt : a -> a -> Bool" $ do
            let ctxtWithGt = ctxtWithAnd
                  & testTcContext <>~ [ TceClass S.empty (TyApp (TyCon $ TypeCon "Gt") $ TyVar "a") undefined ]
                  & over testContext
                    ( M.insert "gt" $
                        _Forall'
                          ["a"]
                          [TyApp (TyCon $ TypeCon "Gt") (TyVar "a")]
                          # _TyFun # (_TyVar # "a", _TyFun # (_TyVar # "a", _TyPrim # Bool))
                    )
            it "\\x. and (eq x x) (gt x x) : forall a. (Eq a, Gt a) => a -> Bool" $ do
              let eqxx = _App # (_App # (_Id # "eq", _Id # "x"), _Id # "x")
                  gtxx = _App # (_App # (_Id # "gt", _Id # "x"), _Id # "x")
              typeOf ctxtWithGt initialTestState (_Abs' "x" # _App # (_App # (_Id # "and", eqxx), gtxx))
                `shouldBe` (Right $
                  Forall
                    (S.singleton "t6")
                    (S.fromList
                      [ TyApp (TyCon $ TypeCon "Eq") (TyVar "t6")
                      , TyApp (TyCon $ TypeCon "Gt") (TyVar "t6")
                      ]
                    )
                    (TyFun (TyVar "t6") $ TyPrim Bool))
