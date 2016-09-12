module Lambda where

import Control.Applicative
import Control.Monad.State
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as M
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as S

type Identifier = String

-- Syntax of expressions
data Expr
  = Id Identifier
  | App Expr Expr
  | Abs Identifier Expr
  | Let Identifier Expr Expr
  deriving (Eq, Show)

-- Primitive types
data Prim
  = Int
  | String
  | Char
  | Bool
  deriving (Eq, Show, Ord)

-- Syntax of types
data Type
  = TypeVar String
  | PrimType Prim
  | FunType Type Type
  | ProdType Type Type
  | SumType Type Type
  | Bottom
  deriving (Eq, Show, Ord)

-- Syntax of type schemes
data TypeScheme
  = Base Type
  | Forall String TypeScheme
  deriving (Eq, Show, Ord)

type Context = Map Identifier TypeScheme

freeInType :: Type -> Set Type
freeInType ty'@TypeVar{} = S.singleton ty'
freeInType (FunType from to) = freeInType from `S.union` freeInType to
freeInType _ = S.empty

freeInScheme :: TypeScheme -> Set Type
freeInScheme (Base ty) = freeInType ty
freeInScheme (Forall name scheme)
  = freeInScheme scheme `S.difference` S.singleton (TypeVar name)

free :: Context -> Set Type
free
  = foldl (\frees (name,ty) -> frees `S.union` freeInScheme ty) S.empty . M.toList

bound :: TypeScheme -> (Type, Set Type)
bound (Base ty) = (ty, S.empty)
bound (Forall name scheme) = S.insert (TypeVar name) <$> bound scheme

type Substitutions = Map Identifier Type

specializeTypes :: Set Type -> Type -> Type -> Bool
specializeTypes names ty ty'
  = evalState (canSpecialize names ty ty') M.empty
  where
    canSpecializeMulti names a a' b b'
      = liftA2 (&&) (canSpecialize names a a') (canSpecialize names b b')

    canSpecialize :: Set Type -> Type -> Type -> State Substitutions Bool
    canSpecialize names ty@(TypeVar name) ty' = do
      sub <- gets $ M.lookup name
      case sub of
        Just ty -> return $ ty == ty'
        Nothing -> do
          let nameInNames = ty `S.member` names
          when nameInNames . modify $ M.insert name ty'
          return nameInNames
    canSpecialize names ty@PrimType{} ty' = return $ ty == ty'
    canSpecialize names (FunType from to) (FunType from' to')
      = canSpecializeMulti names from from' to to'
    canSpecialize names (ProdType one two) (ProdType one' two')
      = canSpecializeMulti names one one' two two'
    canSpecialize names (SumType left right) (SumType left' right')
      = canSpecializeMulti names left left' right right'
    canSpecialize names Bottom ty' = return True
    canSpecialize names _ _ = return False

specialize :: TypeScheme -> TypeScheme -> Bool
specialize (Base ty) s@(Base ty') = ty == ty'
specialize (Base scheme) scheme'
  = freeInType scheme `S.intersection` snd (bound scheme') == S.empty
specialize scheme scheme'@(Base ty')
  = let (ty, tyVars) = bound scheme
    in specializeTypes tyVars ty ty'
specialize scheme scheme'
  = let (ty, tyVars) = bound scheme
        (ty', tyVars') = bound scheme'
    in freeInScheme scheme `S.intersection` tyVars' == S.empty &&
       specializeTypes tyVars ty ty'
