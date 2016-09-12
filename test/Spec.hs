{-# language TemplateHaskell #-}

import Test.QuickCheck
import Lambda hiding (Identifier)
import Lambda.Test.Arbitrary

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

return []
main = $quickCheckAll
