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

type Substitutions = Map Identifier Type

substitute :: Substitutions -> Type -> Type
substitute subs ty@(TypeVar name) = fromMaybe ty (M.lookup name subs)
substitute subs (FunType from to)
  = FunType (substitute subs from) (substitute subs to)
substitute subs ty = ty

instantiate :: Substitutions -> TypeScheme -> TypeScheme
instantiate subs (Base ty) = Base $ substitute subs ty
instantiate subs (Forall name scheme)
  = case M.lookup name subs of
      Just (TypeVar name') -> Forall name' $ instantiate subs scheme
      Just _ -> instantiate subs scheme
      Nothing -> Forall name $ instantiate subs scheme

ge :: TypeScheme -> TypeScheme -> Bool
ge scheme (Base ty) = geGivenBound S.empty scheme ty
  where
    geGivenBound :: Set Identifier -> TypeScheme -> Type -> Bool
    geGivenBound names (Forall name s) t = geGivenBound (S.insert name names) s t
    geGivenBound names (Base t) t' = evalState (ge' names t t') M.empty

    subsAreConsistent :: Map String Type -> Map String Type -> Bool
    subsAreConsistent subs subs'
      = getAll . M.foldMapWithKey (\k a -> All a) $ M.intersectionWith (==) subs subs'

    geGivenNestedSubs :: Set Identifier
                      -> Type -> Type
                      -> Type -> Type
                      -> State Substitutions Bool
    geGivenNestedSubs names a a' b b' = do
      subs <- get
      aRes <- ge' names a a'
      aSubs <- get
      put subs
      bRes <- ge' names b b'
      bSubs <- get
      let subsConsistent = subsAreConsistent aSubs bSubs
      unless subsConsistent $ put subs
      return $ aRes && bRes && subsConsistent

    ge' :: Set Identifier -> Type -> Type -> State Substitutions Bool
    ge' _ _ Bottom = return True
    ge' names (FunType from to) (FunType from' to')
      = geGivenNestedSubs names from from' to to'
    ge' names (ProdType one two) (ProdType one' two')
      = geGivenNestedSubs names one one' two two'
    ge' names (SumType left right) (SumType left' right')
      = geGivenNestedSubs names left left' right right'
    ge' names (TypeVar t) t'
      | t `S.member` names = do
          sub <- gets $ M.lookup t
          case sub of
            Just ty -> return $ ty == t'
            Nothing -> do
              let pred = case t' of
                    TypeVar{} -> not (t' `S.member` freeInScheme scheme)
                    FunType from to -> noFrees from to
                    ProdType one two -> noFrees one two
                    SumType left right -> noFrees left right
                    _ -> True
              when pred . modify $ M.insert t t'
              return pred
      | otherwise = return False
    ge' names _ _ = return False

    noFrees a b
      = let frs = freeInScheme scheme
        in S.null (frs `S.intersection` freeInType a) &&
           S.null (frs `S.intersection` freeInType b)


ge scheme scheme' = boundNotInFree (freeInScheme scheme) scheme'
  where
    boundNotInFree frs (Forall n s)
      = not (TypeVar n `S.member` frs) && boundNotInFree frs s
    boundNotInFree frs s = ge scheme s

type Judgement = (Context,Expr,TypeScheme)
