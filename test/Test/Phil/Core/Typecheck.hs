{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module Test.Phil.Core.Typecheck (typecheckSpec) where

import Control.Lens
import Control.Monad.Except
import Control.Monad.Fresh
import Control.Monad.Reader
import Control.Monad.State
import Data.Either

import qualified Data.Map as M
import qualified Data.Set as S

import Phil.Core.AST.Identifier
import Phil.Core.AST.InstanceHead
import Phil.Core.AST.Lens
import Phil.Core.AST.Types
import Phil.Core.Kinds
import Phil.Typecheck hiding (special)
import Phil.Typecheck.TypeError
import Phil.Typeclasses

import qualified Phil.AST.Binding as L
import qualified Phil.AST.Expr as L
import qualified Phil.Core.AST.Expr as C
import qualified Phil.Typecheck as T (special)

import Test.Hspec

data TestContexts
  = TestContexts
  { _testContext   :: M.Map (Either Ident Ctor) ContextEntry
  , _testTcContext :: [TypeclassEntry C.Expr]
  }

emptyContexts = TestContexts M.empty []

makeClassy ''TestContexts

instance HasContext TestContexts where
  context = testContexts . testContext

instance HasTcContext C.Expr TestContexts where
  tcContext = testContexts . testTcContext

data TestState
  = TestState
  { _tdKindTable      :: M.Map (Either Ident Ctor) Kind
  , _tdFreshCount     :: Int
  , _tdTcContext      :: [TypeclassEntry C.Expr]
  }

initialTestState = TestState M.empty 0 []

makeLenses ''TestState

instance HasKindTable TestState where
  kindTable = tdKindTable . kindTable

instance HasTcContext C.Expr TestState where
  tcContext = tdTcContext

special :: TestContexts -> TypeScheme -> TypeScheme -> Either TypeOrKindError ()
special ctxts scheme scheme'
  = flip evalState initialTestState .
    flip runReaderT ctxts .
    runFreshT .
    runExceptT $
    T.special scheme scheme'

hasType :: L.Expr -> TypeScheme -> Expectation
hasType expr ty = snd <$> runInferTypeScheme expr `shouldSatisfy` (\ty' -> isRight (ty' >>= special emptyContexts ty))

typeOf :: TestContexts -> TestState -> L.Expr -> Either TypeOrKindError TypeScheme
typeOf ctxt st expr
  = flip runReader ctxt .
    runFreshT .
    flip evalStateT st .
    runExceptT $ snd <$> inferTypeScheme expr

typecheckSpec = describe "Phil.Core.Typecheck" $ do
  describe "special" $ do
    let idType = _Forall' [Ident "a"] [] # _TyFun # (_TyVar # Ident "a", _TyVar # Ident "a")
    describe "success" $ do
      it "forall a. a -> a is more general than forall b. b -> b" $
        special
          emptyContexts
          idType
          (_Forall' [Ident "b"] [] # _TyFun # (_TyVar # Ident "b", _TyVar # Ident "b"))

        `shouldSatisfy`

        has _Right

      it "forall a. a -> a is more general than forall a b. b -> b" $
        special
          emptyContexts
          idType
          (_Forall' [Ident "a", Ident "b"] [] # _TyFun # (_TyVar # Ident "b", _TyVar # Ident "b"))

        `shouldSatisfy`

        has _Right

      it "forall a. a -> a is more general than forall a b. Int -> Int" $
        special
          emptyContexts
          idType
          (_Forall' [Ident "a", Ident "b"] [] # _TyFun # (_TyCtor # Ctor "Int", _TyCtor # Ctor "Int"))

        `shouldSatisfy`

        has _Right

      it "forall a. a -> a is more general than Int -> Int" $
        special
          emptyContexts
          idType
          (_Forall' [] [] # _TyFun # (_TyCtor # Ctor "Int", _TyCtor # Ctor "Int"))

        `shouldSatisfy`

        has _Right

      it "forall a. a -> a is more general than forall b c. (b -> c) -> (b -> c)" $
        special emptyContexts idType
          (_Forall' [Ident "b", Ident "c"] []
            # _TyFun
              # ( _TyFun # (_TyVar # Ident "b", _TyVar # Ident "c")
                , _TyFun # (_TyVar # Ident "b", _TyVar # Ident "c"))
          ) `shouldSatisfy` has _Right

    describe "failure" $ do
      it "forall a. a -> a does not unify with forall b c. b -> c" $
        special
          emptyContexts
          idType
          (_Forall' [Ident "b", Ident "c"] [] # _TyFun # (_TyVar # Ident "b", _TyVar # Ident "c"))

        `shouldSatisfy`

        has (_Left . _TUnificationError)

      it "forall a. a -> a does not unify with forall b c d. (b -> c) -> (b -> d)" $
        special emptyContexts idType
          (_Forall' [Ident "b", Ident "c", Ident "d"] []
            # _TyFun
              # ( _TyFun # (_TyVar # Ident "b", _TyVar # Ident "c")
                , _TyFun # (_TyVar # Ident "b", _TyVar # Ident "d"))
          ) `shouldSatisfy` has (_Left . _TUnificationError)

      it "forall a. a -> a does not unify with forall a b f. f a -> f b" $
        special emptyContexts idType
          (_Forall' [Ident "a", Ident "b", Ident "f"] []
            # _TyFun
              # ( _TyApp # (_TyVar # Ident "f", _TyVar # Ident "a")
                , _TyApp # (_TyVar # Ident "f", _TyVar # Ident "b")
                )
          ) `shouldSatisfy` has (_Left . _TUnificationError)

      it "Int -> Int [>=] forall a. a -> a" $
        special
          emptyContexts
          (_Forall' [] [] # _TyFun # (_TyCtor # Ctor "Int", _TyCtor # Ctor "Int"))
          idType

        `shouldSatisfy`

        has (_Left . _TUnificationError)

  describe "typeclass" $ do
    let constrainedId =
          _Forall'
            [Ident "a"]
            [TyApp (TyCon . TypeCon $ Ctor "Constraint") (TyVar $ Ident "a")] #
            _TyFun #
            (_TyVar # Ident "a", _TyVar # Ident "a")

        regularId = _Forall' [Ident "a"] [] # _TyFun # (_TyVar # Ident "a", _TyVar # Ident "a")
        intToInt = _Forall' [] [] # _TyFun # (_TyCtor # Ctor "Int", _TyCtor # Ctor "Int")

    describe "success" $ do
      let ctxt = emptyContexts
            { _testTcContext =
              [ TceClass [] (Ctor "Constraint") (pure $ Ident "b") undefined 
              , TceInst [] (InstanceHead (Ctor "Constraint") $ pure (Ctor "Int", [])) undefined
              ]
            }
      it "forall a. a -> a [>=] forall a. Constraint a => a -> a" $
        special emptyContexts regularId constrainedId `shouldSatisfy` has _Right
      it "forall a. Constraint a => a -> a not [>=] forall a. a -> a" $
        special emptyContexts constrainedId regularId `shouldSatisfy` has _Left
      it "instance Constraint Int where ... ==> forall a. Constraint a => a -> a [>=] Int -> Int" $
        special ctxt constrainedId intToInt `shouldSatisfy` has _Right

    describe "failure" $ do
      let ctxt = emptyContexts
            { _testTcContext = [TceClass [] (Ctor "Constraint") (pure $ Ident "b") undefined ] }
      it "forall a. Constraint a => a -> a [>=] Int -> Int but there is no instance Constraint Int" $
        special ctxt constrainedId intToInt `shouldSatisfy` has (_Left . _CouldNotDeduce)
      let constrainedId = _Forall'
            [Ident "a"]
            [ TyApp (TyCon . TypeCon $ Ctor "Constraint") (TyVar $ Ident "a")
            , TyApp (TyCon . TypeCon $ Ctor "Other") (TyVar $ Ident "a")
            ]
            # _TyFun # (_TyVar # Ident "a", _TyVar # Ident "a")
          ctxt = emptyContexts
            { _testTcContext =
              [ TceClass [] (Ctor "Constraint") (pure $ Ident "b") undefined 
              , TceInst [] (InstanceHead (Ctor "Constraint") $ pure (Ctor "Int", [])) undefined
              ]
            }
      it "instance Constraint Int where ... => forall a. (Constraint a, Other a) => a -> a [>=] Int -> Int but there is no class `Other`" $
        special ctxt constrainedId intToInt `shouldSatisfy` has (_Left . _CouldNotDeduce)

  describe "w" $ do
    describe "success" $ do
      it "\\x. x : forall a. a -> a" $
        L.Abs
          (Ident "x")
          (L.Id (Ident "x"))

        `hasType`

        (_Forall' [Ident "t0"] [] # _TyFun # (_TyVar # Ident "t0", _TyVar # Ident "t0"))

      it "\\x. \\y. x : forall a b. a -> b -> a" $
        L.Abs (Ident "x") (L.Abs (Ident "y") $ L.Id (Ident "x"))

        `hasType`

        (_Forall' [Ident "t0", Ident "t1"] [] # _TyFun # (_TyVar # Ident "t0", _TyFun # (_TyVar # Ident "t1", _TyVar # Ident "t0")))

      it "rec fix f x = f (fix f) x in rec : forall a. (a -> a) -> a" $
        L.Rec
          (L.VariableBinding (Ident "fix") $ L.Abs (Ident "f") $ L.App (L.Id (Ident "f")) $ L.App (L.Id $ Ident "fix") (L.Id (Ident "f")))
          (L.Id $ Ident "fix")

        `hasType`

        (_Forall' [Ident "t4"] [] # _TyFun # (_TyFun # (_TyVar # Ident "t4", _TyVar # Ident "t4"), _TyVar # Ident "t4"))

    describe "failure" $
      it "\\x. x x" $
        runInferTypeScheme (L.Abs (Ident "x") $ L.App (L.Id (Ident "x")) $ L.Id (Ident "x")) `shouldSatisfy` has (_Left . _TUnificationError)

    describe "typeclasses" $
      Test.Hspec.context "class Eq a where eq : a -> a -> Bool where ..." $ do
        let ctxt = emptyContexts
              { _testContext = M.singleton (Left $ Ident "eq") . OEntry $
                  _Forall'
                    [Ident "a"]
                    [TyApp (TyCon . TypeCon $ Ctor "Eq") . TyVar $ Ident "a"]
                    # _TyFun # (_TyVar # Ident "a", _TyFun # (_TyVar # Ident "a", _TyCtor # Ctor "Bool"))
              , _testTcContext =
                  [ TceClass [] (Ctor "Eq") (pure $ Ident "a") undefined ]
              }
        it "\\x. \\y. eq y x : forall a. Eq a => a -> a -> Bool" $
          typeOf
            ctxt
            initialTestState
            (L.Abs (Ident "x") $ L.Abs (Ident "y") $ L.App (L.App (L.Id $ Ident "eq") $ L.Id (Ident "y")) $ L.Id (Ident "x"))

          `shouldBe`

          (Right $
            Forall
              (S.singleton $ Ident "t4")
              [TyApp (TyCon $ TypeCon $ Ctor "Eq") (TyVar $ Ident "t4")]
              (TyFun (TyVar $ Ident "t4") $ TyFun (TyVar $ Ident "t4") (TyCtor $ Ctor "Bool")))

        it "\\x. eq x x : forall a. Eq a => a -> Bool" $
          typeOf
            ctxt
            initialTestState
            (L.Abs (Ident "x") $ L.App (L.App (L.Id $ Ident "eq") $ L.Id (Ident "x")) $ L.Id (Ident "x"))

          `shouldBe`

          (Right $
            Forall
              (S.singleton $ Ident "t2")
              [TyApp (TyCon . TypeCon $ Ctor "Eq") (TyVar $ Ident "t2")]
              (TyFun (TyVar $ Ident "t2") (TyCtor $ Ctor "Bool")))

        Test.Hspec.context "and : Bool -> Bool -> Bool" $ do
          let ctxtWithAnd = ctxt & over testContext
                ( M.insert (Left $ Ident "and" ) . FEntry $
                    _Forall' [] []
                      # _TyFun # (_TyCtor # Ctor "Bool", _TyFun # (_TyCtor # Ctor "Bool", _TyCtor # Ctor "Bool"))
                )
          it "\\x y. and (eq x x) (eq y y) : forall a a1. (Eq a, Eq a1) => a -> a1 -> Bool" $ do
            let eqxx = L.App (L.App (L.Id $ Ident "eq") $ L.Id (Ident "x")) $ L.Id (Ident "x")
                eqyy = L.App (L.App (L.Id $ Ident "eq") $ L.Id (Ident "y")) $ L.Id (Ident "y")
            typeOf
              ctxtWithAnd
              initialTestState
              (L.Abs (Ident "x") $ L.Abs (Ident "y") $ L.App (L.App (L.Id $ Ident "and") eqxx) eqyy)

            `shouldBe`

            (Right $
              Forall
                (S.fromList [Ident "t4", Ident "t12"])
                [ TyApp (TyCon . TypeCon $ Ctor "Eq") (TyVar (Ident "t4"))
                , TyApp (TyCon . TypeCon $ Ctor "Eq") (TyVar (Ident "t12"))
                ]
                (TyFun (TyVar (Ident "t4")) $ TyFun (TyVar (Ident "t12")) $ TyCtor (Ctor "Bool")))

          Test.Hspec.context "class Gt a where gt : a -> a -> Bool" $ do
            let ctxtWithGt = ctxtWithAnd
                  & testTcContext <>~ [ TceClass [] (Ctor "Gt") (pure $ Ident "a") undefined ]
                  & over testContext
                    ( M.insert (Left $ Ident "gt") . OEntry $
                        _Forall'
                          [Ident "a"]
                          [TyApp (TyCon $ TypeCon (Ctor "Gt")) (TyVar (Ident "a"))]
                          # _TyFun # (_TyVar # Ident "a", _TyFun # (_TyVar # Ident "a", _TyCtor # Ctor "Bool"))
                    )
            it "\\x. and (eq x x) (gt x x) : forall a. (Eq a, Gt a) => a -> Bool" $ do
              let eqxx = L.App (L.App (L.Id (Ident "eq")) $ L.Id (Ident "x")) $ L.Id (Ident "x")
                  gtxx = L.App (L.App (L.Id (Ident "gt")) $ L.Id (Ident "x")) $ L.Id (Ident "x")
              typeOf ctxtWithGt initialTestState (L.Abs (Ident "x") $ L.App (L.App (L.Id (Ident "and")) eqxx) gtxx)
                `shouldBe` (Right $
                  Forall
                    (S.singleton $ Ident "t10")
                    [ TyApp (TyCon $ TypeCon (Ctor "Eq")) (TyVar (Ident "t10"))
                    , TyApp (TyCon $ TypeCon (Ctor "Gt")) (TyVar (Ident "t10"))
                    ]
                    (TyFun (TyVar (Ident "t10")) $ TyCtor (Ctor "Bool")))
