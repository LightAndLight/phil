{-# LANGUAGE TemplateHaskell #-}

import           Control.Monad.Except
import           Control.Monad.State
import           Data.Either
import           Data.List.NonEmpty       (NonEmpty (..))
import           Data.Map                 (Map)
import qualified Data.Map                 as M
import qualified Data.Set                 as S
import           Lambda
import           Lambda.Core              hiding (Identifier)
import           Lambda.Test.Arbitrary
import           Test.QuickCheck
import qualified Test.QuickCheck.Property as P

import           Debug.Trace

runW :: Expr -> Either InferenceError TypeScheme
runW = runExcept . flip evalStateT (InferenceState M.empty M.empty 0) . w

runWith :: Map String TypeScheme -> Map String Int -> Expr -> Either InferenceError TypeScheme
runWith ctxt tys = runExcept . flip evalStateT (InferenceState ctxt tys 0) . w

runWith' :: Map String TypeScheme -> Map String Int -> Expr -> Either InferenceError (TypeScheme, Map String TypeScheme)
runWith' ctxt tys = fmap (fmap _context) . runExcept . flip runStateT (InferenceState ctxt tys 0) . w

constType :: Identifier -> Identifier -> TypeScheme
constType (Identifier a) (Identifier b)
  = Forall a . Forall b . Base $
      FunType (TypeVar a) (FunType (TypeVar b) (TypeVar a))

constTypeFlippedBinding :: Identifier -> Identifier -> TypeScheme
constTypeFlippedBinding (Identifier a) (Identifier b)
  = Forall b . Forall a . Base $
      FunType (TypeVar a) (FunType (TypeVar b) (TypeVar a))

constTypeSubbedB :: Identifier -> Type -> TypeScheme
constTypeSubbedB (Identifier a) b
  = Forall a . Base $
      FunType (TypeVar a) (FunType b (TypeVar a))

constTypeSubbedAB :: Type -> Type -> TypeScheme
constTypeSubbedAB a b = Base $ FunType a (FunType b a)

prop_specialize_equivalent :: Identifier
                     -> Identifier
                     -> Identifier
                     -> Identifier
                     -> Property
prop_specialize_equivalent a b a' b'
  = a /= b && a' /= b'
    ==> let right = constType a' b'
        in specialize (constType a b) right

prop_specialize_vars_refl :: Identifier -> Identifier -> Property
prop_specialize_vars_refl a b
  = a /= b ==> let ty = constType a b in specialize ty ty

prop_specialize_refl :: Type -> Bool
prop_specialize_refl ty
  = let scheme = Base ty in specialize scheme scheme

prop_specialize_bad :: Type -> Type -> Property
prop_specialize_bad ty ty'
  = ty /= ty' ==> not (specialize (Base ty) (Base ty'))

prop_specialize_const_good :: Identifier -> Identifier -> Type -> Property
prop_specialize_const_good a b b'
  = a /= b
    ==> let right = constTypeSubbedB a b'
        in specialize (constType a b) right

prop_specialize_const_bad :: Identifier
                          -> Type
                          -> Type
                          -> Property
prop_specialize_const_bad a b b'
  = b /= b' ==> not (specialize (constTypeSubbedB a b) (constTypeSubbedB a b'))

prop_occurs_fail :: Identifier -> Bool
prop_occurs_fail (Identifier a) = isLeft $ runW (Abs a (App (Id a) (Id a)))

prop_case_inference1 :: Bool
prop_case_inference1 = left == right
  where
    left = Right $ Base (PrimType String)
    right = runW
      (App
        (PatAbs (PatLit $ LitInt 0) (Lit $ LitString "hello"))
        (Lit $ LitInt 1))

prop_case_inference2 :: Bool
prop_case_inference2 = left == right
  where
    left = Right $ Base (FunType (PrimType Int) (PrimType String))
    right = runW
      (Abs "x"
        (App
          (PatAbs (PatLit $ LitInt 0) (Lit $ LitString "hello"))
          (Id "x")))

prop_case_wrong_pattern_type1 :: Bool
prop_case_wrong_pattern_type1 = isLeft res
  where
    res = runW
      (Chain
        (App (PatAbs (PatLit $ LitInt 0) (Lit $ LitString "yes")) (Lit $ LitInt 1))
        (App (PatAbs (PatLit $ LitString "asdf") (Lit $ LitString "no")) (Lit $ LitInt 1)))

prop_case_wrong_pattern_type2 :: Bool
prop_case_wrong_pattern_type2 = isLeft res
  where
    res = runW
      (Abs "x" (Chain
        (App (PatAbs (PatLit $ LitInt 0) (Lit $ LitString "yes")) (Id "x"))
        (App (PatAbs (PatLit $ LitString "asdf") (Lit $ LitString "no")) (Id "x"))))

prop_case_wrong_branch_type :: Bool
prop_case_wrong_branch_type = isLeft res
  where
    res = runW
      (Chain
        (App (PatAbs (PatLit $ LitInt 0) (Lit $ LitString "yes")) (Lit $ LitString "blah"))
        (App (PatAbs (PatLit $ LitInt 1) (Lit $ LitString "no")) (Lit $ LitInt 1)))

prop_pat_abs_inference :: P.Result
prop_pat_abs_inference
  = correct $ runWith context tys $ PatAbs (PatCon "U" ["a","b"]) $ Id "b"
  where
    tys = M.fromList [("T", 4)]
    u =
      Forall "a" $ Forall "b" $ Forall "c" $ Forall "d" $ Base $
        FunType (TypeVar "a") $
        FunType (TypeVar "b") $
        PolyType "T" [TypeVar "a", TypeVar "b", TypeVar "c", TypeVar "d"]
    v =
      Forall "a" $ Forall "b" $ Forall "c" $ Forall "d" $ Base $
        FunType (TypeVar "c") $
        FunType (TypeVar "d") $
        PolyType "T" [TypeVar "a", TypeVar "b", TypeVar "c", TypeVar "d"]
    context = M.fromList
      [ ("U", u)
      , ("V", v)
      ]
    correct (Right (Forall a (Forall b (Forall c (Forall d (Base (FunType (PolyType t args) v)))))))
      = P.liftBool $ length args == 4 &&
          args !! 1 == v &&
          S.fromList args == S.fromList (fmap TypeVar [a,b,c,d])
    correct (Right ty) = P.failed { P.reason = "Incorrect type inferred: " ++ showTypeScheme ty }
    correct (Left e) = P.failed { P.reason = "Type inference failed: " ++ show e }

prop_pat_abs_abs_inference :: P.Result
prop_pat_abs_abs_inference
  = correct $ runWith context tys $ Abs "x" $ App (PatAbs (PatCon "U" ["a","b"]) $ Id "b") $ Id "x"
  where
    tys = M.fromList [("T", 4)]
    u =
      Forall "a" $ Forall "b" $ Forall "c" $ Forall "d" $ Base $
        FunType (TypeVar "a") $
        FunType (TypeVar "b") $
        PolyType "T" [TypeVar "a", TypeVar "b", TypeVar "c", TypeVar "d"]
    v =
      Forall "a" $ Forall "b" $ Forall "c" $ Forall "d" $ Base $
        FunType (TypeVar "c") $
        FunType (TypeVar "d") $
        PolyType "T" [TypeVar "a", TypeVar "b", TypeVar "c", TypeVar "d"]
    context = M.fromList
      [ ("U", u)
      , ("V", v)
      ]
    correct (Right (Forall a (Forall b (Forall c (Forall d (Base (FunType (PolyType t args) v)))))))
      = P.liftBool $ length args == 4 &&
          args !! 1 == v &&
          S.fromList args == S.fromList (fmap TypeVar [a,b,c,d])
    correct (Right ty) = P.failed { P.reason = "Incorrect type inferred: " ++ showTypeScheme ty }
    correct (Left e) = P.failed { P.reason = "Type inference failed: " ++ show e }

prop_pat_abs_app_arg_inference :: P.Result
prop_pat_abs_app_arg_inference
  = correct $ (runExcept . flip runStateT (InferenceState context tys 1) . w) $ App (PatAbs (PatCon "U" ["a","b"]) $ Id "b") $ Id "x"
  where
    tys = M.fromList [("T", 4)]
    u =
      Forall "a" $ Forall "b" $ Forall "c" $ Forall "d" $ Base $
        FunType (TypeVar "a") $
        FunType (TypeVar "b") $
        PolyType "T" [TypeVar "a", TypeVar "b", TypeVar "c", TypeVar "d"]
    v =
      Forall "a" $ Forall "b" $ Forall "c" $ Forall "d" $ Base $
        FunType (TypeVar "c") $
        FunType (TypeVar "d") $
        PolyType "T" [TypeVar "a", TypeVar "b", TypeVar "c", TypeVar "d"]
    context = M.fromList
      [ ("U", u)
      , ("V", v)
      , ("x", Base $ TypeVar "t0")
      ]
    correct (Right (Forall a (Forall b (Forall c (Forall d (Base (FunType (PolyType t args) v))))), st))
      = P.liftBool $ length args == 4 &&
          args !! 1 == v &&
          S.fromList args == S.fromList (fmap TypeVar [a,b,c,d]) &&
          M.member "x" (seq (traceShowId $ M.lookup "x" $ _context st) $ _context st)
    correct (Right (ty, _)) = P.failed { P.reason = "Incorrect type inferred: " ++ showTypeScheme ty }
    correct (Left e) = P.failed { P.reason = "Type inference failed: " ++ show e }

return []
main = $quickCheckAll
