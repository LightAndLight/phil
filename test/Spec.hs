{-# LANGUAGE TemplateHaskell #-}

import           Data.Either
import           Data.List.NonEmpty    (NonEmpty (..))
import qualified Data.Map              as M
import qualified Data.Set              as S

import           Lambda.Core.AST       hiding (Identifier)
import           Lambda.Core.Typecheck
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

prop_specialize_equivalent
  :: Identifier
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

prop_specialize_const_bad
  :: Identifier
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
    right = runW (Case (Lit (LitInt 1)) ((PatLit (LitInt 0),Lit (LitString "hello")) :| []))

prop_case_inference2 :: Bool
prop_case_inference2 = left == right
  where
    left = Right $ Base (FunType (PrimType Int) (PrimType String))
    right = runW (Abs "x" $ Case (Id "x") ((PatLit (LitInt 0),Lit (LitString "hello")) :| []))

prop_case_complicated_inference1 :: Bool
prop_case_complicated_inference1 = correct $ runWithContext ctxt ast
  where
    u = Forall "a" $ Forall "b" $ Forall "c" $ Forall "d" $ Base $
      FunType (TypeVar "a") $
      FunType (TypeVar "b") $
      PolyType "T" [TypeVar "a", TypeVar "b", TypeVar "c", TypeVar "d"]
    v = Forall "a" $ Forall "b" $ Forall "c" $ Forall "d" $ Base $
      FunType (TypeVar "c") $
      FunType (TypeVar "d") $
      PolyType "T" [TypeVar "a", TypeVar "b", TypeVar "c", TypeVar "d"]
    ctxt = M.fromList [("U",u), ("V",v)]
    ast = Abs "x" $ Abs "y" $ Case (Id "x") $
      (PatCon "U" ["a", "b"],Id "a") :|
      [ (PatWildcard,Id "y")
      , (PatCon "V" ["a","b"],Id "a")
      ]

    correct :: Either TypeError TypeScheme -> Bool
    correct (Right (Forall a (Forall b (Forall c (Base (FunType (PolyType t [TypeVar one, TypeVar two, TypeVar three, TypeVar four]) (FunType (TypeVar y) (TypeVar z))))))))
      = all (== z) [one, three, y] &&
        two `elem` [a,b,c] &&
        four `elem` [a,b,c] &&
        z `elem` [a,b,c] &&
        length (S.fromList [two,four,z]) == 3 &&
        length (S.fromList [a,b,c]) == 3
    correct _ = False

prop_case_wrong_pattern_type1 :: Bool
prop_case_wrong_pattern_type1 = isLeft res
  where
    res = runW (Case (Lit (LitInt 1))
      ((PatLit (LitInt 0),Lit (LitString "yes")) :|
        [(PatLit (LitString "asdf"),Lit (LitString "no"))]))

prop_case_wrong_pattern_type2 :: Bool
prop_case_wrong_pattern_type2 = isLeft res
  where
    res = runW (Abs "x" $ Case (Id "x")
      ((PatLit (LitInt 0),Lit (LitString "yes")) :|
        [(PatLit (LitString "asdf"),Lit (LitString "no"))]))

prop_case_wrong_branch_type :: Bool
prop_case_wrong_branch_type = isLeft res
  where
    res = runW (Case (Lit (LitInt 1))
      ((PatLit (LitInt 0),Lit (LitString "blah"))
        :| [(PatLit (LitInt 1),Lit (LitInt 0))]))

return []
main = $quickCheckAll
