{-# LANGUAGE TemplateHaskell #-}

import           Data.Either
import           Data.List.NonEmpty    (NonEmpty (..))
import qualified Data.Map              as M
import           Lambda
import           Lambda.Core           hiding (Identifier)
import           Lambda.Test.Arbitrary
import           Test.QuickCheck

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

return []
main = $quickCheckAll
