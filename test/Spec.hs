{-# language TemplateHaskell #-}

import Test.QuickCheck
import Lambda

instance Arbitrary Prim where
  arbitrary = elements [Int,String,Char,Bool]

constType :: Identifier -> Identifier -> TypeScheme
constType a b
  = Forall a . Forall b . Base $
      FunType (TypeVar a) (FunType (TypeVar b) (TypeVar a))

constTypeFlippedBinding :: Identifier -> Identifier -> TypeScheme
constTypeFlippedBinding a b
  = Forall b . Forall a . Base $
      FunType (TypeVar a) (FunType (TypeVar b) (TypeVar a))

constTypeSubbedA :: Identifier -> Prim -> TypeScheme
constTypeSubbedA a prim
  = Forall a . Base $
      FunType (TypeVar a) (FunType (PrimType prim) (TypeVar a))

constTypeSubbedB :: Identifier -> Prim -> TypeScheme
constTypeSubbedB b prim
  = Forall b . Base $
      FunType (PrimType prim) (FunType (TypeVar b) (PrimType prim))

constTypeSubbedAB :: Prim -> Prim -> TypeScheme
constTypeSubbedAB a b
  = Base $
      FunType (PrimType a) (FunType (PrimType b) (PrimType a))

prop_ge_const1 :: Identifier -> Identifier -> Prim -> Bool
prop_ge_const1 a b prim = constType a b `ge` constTypeSubbedA a prim

prop_ge_const2 :: Identifier -> Identifier -> Prim -> Bool
prop_ge_const2 a b prim = constType a b `ge` constTypeSubbedB b prim

prop_ge_const3 :: Identifier -> Identifier -> Prim -> Bool
prop_ge_const3 a b prim = constTypeSubbedA a prim `ge` constTypeSubbedB b prim

prop_ge_swap_bindings_refl :: Identifier
                           -> Identifier
                           -> Identifier
                           -> Identifier
                           -> Bool
prop_ge_swap_bindings_refl a b a' b'
  = constType a b `ge` constType b a &&
    constType b a `ge` constType a b &&
    constType a b `ge` constType a' b' &&
    constType a' b' `ge` constType a b

prop_mono_not_ge_mono :: Prim
                      -> Prim
                      -> Prim
                      -> Prim
                      -> Bool
prop_mono_not_ge_mono a b a' b'
  = not (constTypeSubbedAB a b `ge` constTypeSubbedAB a' b') &&
    not (constTypeSubbedAB a' b' `ge` constTypeSubbedAB a b)

prop_binding_order_irrelevant :: Identifier
                              -> Identifier
                              -> Bool
prop_binding_order_irrelevant a b = constType a b `ge` constTypeFlippedBinding a b

return []
main = $quickCheckAll
