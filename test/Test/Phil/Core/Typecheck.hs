{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}

module Test.Phil.Core.Typecheck (typecheckSpec) where

import Control.Lens
import Control.Monad.Except
import Control.Monad.Fresh
import Control.Monad.Reader
import Control.Monad.State
import Data.Either
import Data.Maybe

import qualified Data.Map                   as M
import qualified Data.Set                   as S

import Phil.Core.AST.Identifier
import Phil.Core.AST.InstanceHead
import Phil.Core.AST.Lens
import Phil.Core.AST.Types
import Phil.Core.Kinds        
import Phil.Typecheck      hiding (special)
import Phil.Typecheck.TypeError
import Phil.Typeclasses

import qualified Phil.AST.Binding as L
import qualified Phil.AST.Expr as L
import qualified Phil.Core.AST.Expr as C
import qualified Phil.Typecheck      as T (special)

import Test.Hspec

data TestContexts
  = TestContexts
  { _testContext   :: M.Map Identifier ContextEntry
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
  { _tdKindTable      :: M.Map Identifier Kind
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
    let idType = _Forall' ["a"] [] # _TyFun # (_TyVar # "a", _TyVar # "a")
    describe "success" $ do
      it "forall a. a -> a is more general than forall b. b -> b" $
        special emptyContexts idType (_Forall' ["b"] [] # _TyFun # (_TyVar # "b", _TyVar # "b")) `shouldSatisfy` has _Right

      it "forall a. a -> a is more general than forall a b. b -> b" $
        special emptyContexts idType (_Forall' ["a","b"] [] # _TyFun # (_TyVar # "b", _TyVar # "b")) `shouldSatisfy` has _Right

      it "forall a. a -> a is more general than forall a b. Int -> Int" $
        special emptyContexts idType (_Forall' ["a","b"] [] # _TyFun # (_TyCtor # "Int", _TyCtor # "Int")) `shouldSatisfy` has _Right

      it "forall a. a -> a is more general than Int -> Int" $
        special emptyContexts idType (_Forall' [] [] # _TyFun # (_TyCtor # "Int", _TyCtor # "Int")) `shouldSatisfy` has _Right

      it "forall a. a -> a is more general than forall b c. (b -> c) -> (b -> c)" $
        special emptyContexts idType
          (_Forall' ["b", "c"] []
            # _TyFun
              # ( _TyFun # (_TyVar # "b", _TyVar # "c")
                , _TyFun # (_TyVar # "b", _TyVar # "c"))
          ) `shouldSatisfy` has _Right

    describe "failure" $ do
      it "forall a. a -> a does not unify with forall b c. b -> c" $
        special emptyContexts idType (_Forall' ["b", "c"] [] # _TyFun # (_TyVar # "b", _TyVar # "c")) `shouldSatisfy` has (_Left . _TUnificationError)

      it "forall a. a -> a does not unify with forall b c d. (b -> c) -> (b -> d)" $
        special emptyContexts idType
          (_Forall' ["b", "c", "d"] []
            # _TyFun
              # ( _TyFun # (_TyVar # "b", _TyVar # "c")
                , _TyFun # (_TyVar # "b", _TyVar # "d"))
          ) `shouldSatisfy` has (_Left . _TUnificationError)

      it "forall a. a -> a does not unify with forall a b f. f a -> f b" $
        special emptyContexts idType
          (_Forall' ["a", "b", "f"] []
            # _TyFun
              # ( _TyApp # (_TyVar # "f", _TyVar # "a")
                , _TyApp # (_TyVar # "f", _TyVar # "b")
                )
          ) `shouldSatisfy` has (_Left . _TUnificationError)

      it "Int -> Int [>=] forall a. a -> a" $
        special emptyContexts (_Forall' [] [] # _TyFun # (_TyCtor # "Int", _TyCtor # "Int")) idType `shouldSatisfy` has (_Left . _TUnificationError)

  describe "typeclass" $ do
    let constrainedId = _Forall' ["a"] [TyApp (TyCon $ TypeCon "Constraint") (TyVar "a")] # _TyFun # (_TyVar # "a", _TyVar # "a")
        regularId = _Forall' ["a"] [] # _TyFun # (_TyVar # "a", _TyVar # "a")
        intToInt = _Forall' [] [] # _TyFun # (_TyCtor # "Int", _TyCtor # "Int")

    describe "success" $ do
      let ctxt = emptyContexts
            { _testTcContext =
              [ TceClass [] "Constraint" (pure "b") undefined 
              , TceInst [] (InstanceHead "Constraint" $ pure ("Int", [])) undefined
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
            { _testTcContext = [TceClass [] "Constraint" (pure "b") undefined ] }
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
              [ TceClass [] "Constraint" (pure "b") undefined 
              , TceInst [] (InstanceHead "Constraint" $ pure ("Int", [])) undefined
              ]
            }
      it "instance Constraint Int where ... => forall a. (Constraint a, Other a) => a -> a [>=] Int -> Int but there is no class `Other`" $
        special ctxt constrainedId intToInt `shouldSatisfy` has (_Left . _CouldNotDeduce)

  describe "w" $ do
    describe "success" $ do
      it "\\x. x : forall a. a -> a" $
        L.Abs "x" (L.Id "x") `hasType` (_Forall' ["t0"] [] # _TyFun # (_TyVar # "t0", _TyVar # "t0"))
      it "\\x. \\y. x : forall a b. a -> b -> a" $
        L.Abs "x" (L.Abs "y" $ L.Id "x")
          `hasType` (_Forall' ["t0","t1"] [] # _TyFun # (_TyVar # "t0", _TyFun # (_TyVar # "t1", _TyVar # "t0")))
      it "rec fix f x = f (fix f) x in rec : forall a. (a -> a) -> a" $
        L.Rec (L.VariableBinding "fix" $ L.Abs "f" $ L.App (L.Id "f") $ L.App (L.Id "fix") (L.Id "f")) (L.Id "fix")
          `hasType` (_Forall' ["t4"] [] # _TyFun # (_TyFun # (_TyVar # "t4", _TyVar # "t4"), _TyVar # "t4"))

    describe "failure" $
      it "\\x. x x" $
        runInferTypeScheme (L.Abs "x" $ L.App (L.Id "x") $ L.Id "x") `shouldSatisfy` has (_Left . _TUnificationError)

    describe "typeclasses" $
      Test.Hspec.context "class Eq a where eq : a -> a -> Bool where ..." $ do
        let ctxt = emptyContexts
              { _testContext = M.singleton "eq" . OEntry $
                  _Forall'
                    ["a"]
                    [TyApp (TyCon $ TypeCon "Eq") $ TyVar "a"]
                    # _TyFun # (_TyVar # "a", _TyFun # (_TyVar # "a", _TyCtor # "Bool"))
              , _testTcContext =
                  [ TceClass [] "Eq" (pure "a") undefined ]
              }
        it "\\x. \\y. eq y x : forall a. Eq a => a -> a -> Bool" $
          typeOf ctxt initialTestState (L.Abs "x" $ L.Abs "y" $ L.App (L.App (L.Id "eq") $ L.Id "y") $ L.Id "x")
            `shouldBe` (Right $
              Forall
                (S.singleton "t4")
                [TyApp (TyCon $ TypeCon "Eq") (TyVar "t4")]
                (TyFun (TyVar "t4") $ TyFun (TyVar "t4") (TyCtor "Bool")))
        it "\\x. eq x x : forall a. Eq a => a -> Bool" $
          typeOf ctxt initialTestState (L.Abs "x" $ L.App (L.App (L.Id "eq") $ L.Id "x") $ L.Id "x")
            `shouldBe` (Right $
              Forall
                (S.singleton "t2")
                [TyApp (TyCon $ TypeCon "Eq") (TyVar "t2")]
                (TyFun (TyVar "t2") (TyCtor "Bool")))
        Test.Hspec.context "and : Bool -> Bool -> Bool" $ do
          let ctxtWithAnd = ctxt & over testContext
                ( M.insert "and" . FEntry $
                    _Forall' [] []
                      # _TyFun # (_TyCtor # "Bool", _TyFun # (_TyCtor # "Bool", _TyCtor # "Bool"))
                )
          it "\\x y. and (eq x x) (eq y y) : forall a a1. (Eq a, Eq a1) => a -> a1 -> Bool" $ do
            let eqxx = L.App (L.App (L.Id "eq") $ L.Id "x") $ L.Id "x"
                eqyy = L.App (L.App (L.Id "eq") $ L.Id "y") $ L.Id "y"
            typeOf ctxtWithAnd initialTestState (L.Abs "x" $ L.Abs "y" $ L.App (L.App (L.Id "and") eqxx) eqyy)
              `shouldBe` (Right $
                Forall
                  (S.fromList ["t4", "t12"])
                  [ TyApp (TyCon $ TypeCon "Eq") (TyVar "t4")
                  , TyApp (TyCon $ TypeCon "Eq") (TyVar "t12")
                  ]
                  (TyFun (TyVar "t4") $ TyFun (TyVar "t12") $ TyCtor "Bool"))
          Test.Hspec.context "class Gt a where gt : a -> a -> Bool" $ do
            let ctxtWithGt = ctxtWithAnd
                  & testTcContext <>~ [ TceClass [] "Gt" (pure "a") undefined ]
                  & over testContext
                    ( M.insert "gt" . OEntry $
                        _Forall'
                          ["a"]
                          [TyApp (TyCon $ TypeCon "Gt") (TyVar "a")]
                          # _TyFun # (_TyVar # "a", _TyFun # (_TyVar # "a", _TyCtor # "Bool"))
                    )
            it "\\x. and (eq x x) (gt x x) : forall a. (Eq a, Gt a) => a -> Bool" $ do
              let eqxx = L.App (L.App (L.Id "eq") $ L.Id "x") $ L.Id "x"
                  gtxx = L.App (L.App (L.Id "gt") $ L.Id "x") $ L.Id "x"
              typeOf ctxtWithGt initialTestState (L.Abs "x" $ L.App (L.App (L.Id "and") eqxx) gtxx)
                `shouldBe` (Right $
                  Forall
                    (S.singleton "t10")
                    [ TyApp (TyCon $ TypeCon "Eq") (TyVar "t10")
                    , TyApp (TyCon $ TypeCon "Gt") (TyVar "t10")
                    ]
                    (TyFun (TyVar "t10") $ TyCtor "Bool"))
