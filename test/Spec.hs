{-# language DeriveFunctor #-}
{-# language TemplateHaskell #-}

import Control.Monad.Free
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

constTypeSubbedA :: Identifier -> Type -> TypeScheme
constTypeSubbedA (Identifier a) ty
  = Forall a . Base $
      FunType (TypeVar a) (FunType ty (TypeVar a))

constTypeSubbedB :: Identifier -> Type -> TypeScheme
constTypeSubbedB (Identifier b) ty
  = Forall b . Base $
      FunType ty (FunType (TypeVar b) ty)

constTypeSubbedAB :: Type -> Type -> TypeScheme
constTypeSubbedAB a b = Base $ FunType a (FunType b a)

idType :: Identifier -> TypeScheme
idType (Identifier a) = Forall a . Base $ FunType (TypeVar a) (TypeVar a)

idTypeSubbedIncorrect :: Type -> Type -> TypeScheme
idTypeSubbedIncorrect a b = Base $ FunType a b

prop_ge_id1 :: Identifier -> Type -> Type -> Property
prop_ge_id1 a a' b' = a' /= b' ==> not (idType a `ge` idTypeSubbedIncorrect a' b')

prop_ge_const1 :: Identifier -> Identifier -> Type -> Bool
prop_ge_const1 a b prim = constType a b `ge` constTypeSubbedA a prim

prop_ge_const2 :: Identifier -> Identifier -> Type -> Bool
prop_ge_const2 a b prim = constType a b `ge` constTypeSubbedB b prim

prop_ge_const3 :: Identifier -> Identifier -> Type -> Bool
prop_ge_const3 a b prim = constTypeSubbedA a prim `ge` constTypeSubbedB b prim

prop_ge_const4 :: Type -> Type -> Identifier -> Property
prop_ge_const4 a a' b = a /= a' ==> not (constTypeSubbedA b a `ge` constTypeSubbedA b a')

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

prop_mono_not_ge_mono :: Type
                      -> Type
                      -> Type
                      -> Type
                      -> Bool
prop_mono_not_ge_mono a b a' b'
  = not (constTypeSubbedAB a b `ge` constTypeSubbedAB a' b') &&
    not (constTypeSubbedAB a' b' `ge` constTypeSubbedAB a b)

prop_binding_order_irrelevant :: Identifier
                              -> Identifier
                              -> Bool
prop_binding_order_irrelevant a b = constType a b `ge` constTypeFlippedBinding a b

fstType :: String -> String -> TypeScheme
fstType a b = Forall a . Forall b $
  Base (FunType (ProdType (TypeVar a) (TypeVar b)) (TypeVar a))

fstTypeSubbedA :: Type -> String -> TypeScheme
fstTypeSubbedA a b = Forall b $
  Base (FunType (ProdType a (TypeVar b)) a)

fstTypeSubbedB :: String -> Type -> TypeScheme
fstTypeSubbedB a b = Forall a $
  Base (FunType (ProdType (TypeVar a) b) (TypeVar a))

prop_ge_fst1 :: Identifier -> Identifier -> Type -> Property
prop_ge_fst1 (Identifier a) (Identifier b) ty
  = a /= b ==> fstType a b `ge`
      Forall a (Forall b
        (Base (FunType
          (ProdType (ProdType (TypeVar a) ty) (TypeVar b))
          (ProdType (TypeVar a) ty))))

prop_ge_fst2 :: Identifier -> Identifier -> Type -> Type -> Property
prop_ge_fst2 (Identifier a) (Identifier b) ty ty'
  = a /= b && ty /= ty' ==> not (fstType a b `ge`
      Forall a (Forall b
        (Base (FunType
          (ProdType (ProdType (TypeVar a) ty) (TypeVar b))
          (ProdType (TypeVar a) ty')))))

prop_ge_fst3 :: Identifier -> Identifier -> Identifier -> Property
prop_ge_fst3 (Identifier a) (Identifier b) (Identifier c)
  = a /= b && a /= c ==> fstType a b `ge`
      Forall a (Forall b (Forall c
        (Base (FunType
          (ProdType (ProdType (TypeVar a) (TypeVar b)) (TypeVar c))
          (ProdType (TypeVar a) (TypeVar b))))))

prop_ge_fst4 :: Identifier -> Identifier -> Type -> Property
prop_ge_fst4 (Identifier a) (Identifier b) b' = a /= b ==> fstType a b `ge` fstTypeSubbedB a b'

prop_ge_fst5 :: Identifier -> Identifier -> Property
prop_ge_fst5 (Identifier a) (Identifier b)
  = a /= b ==> fstType a b `ge` fstTypeSubbedA (ProdType (TypeVar a) (TypeVar a)) b

prop_ge_fst6 :: Identifier -> Identifier -> Property
prop_ge_fst6 (Identifier a) (Identifier b)
  = a /= b ==> fstType a b `ge` fstTypeSubbedB a (FunType (TypeVar b) (TypeVar b))

return []
main = $quickCheckAll
