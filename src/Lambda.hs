{-# language FlexibleContexts #-}

module Lambda where

import Control.Applicative
import Control.Monad.Except
import Control.Monad.State
import Data.Foldable
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as M
import Data.Monoid
import Data.Traversable
import Data.Set (Set)
import qualified Data.Set as S

import Debug.Trace

type Identifier = String

data Pattern = PatId Identifier
             | PatCon Identifier [Identifier]
             | PatLit Literal
             deriving (Eq, Show)

lookupId :: (MonadError InferenceError m, MonadState Context m) => Identifier -> m TypeScheme
lookupId name = do
  maybeTy <- gets $ M.lookup name
  case maybeTy of
    Just ty -> return ty
    Nothing -> throwError $ NotInScope name

conArgTypes :: TypeScheme -> Maybe (Type,[Type])
conArgTypes scheme = uncurry conArgTypes' $ bound scheme
  where
    conArgTypes' :: Type -> Set Identifier -> Maybe (Type,[Type])
    conArgTypes' (FunType from@(TypeVar name) to) bound
      | name `S.member` bound = fmap (from :) <$> conArgTypes' to bound
      | otherwise = Nothing
    conArgTypes' (FunType from to) bound = fmap (from :) <$> conArgTypes' to bound
    conArgTypes' ty@PolyType{} bound = Just (ty,[])
    conArgTypes' _ _ = Nothing

patType :: (MonadError InferenceError m, MonadState Context m)
        => Type
        -> Pattern
        -> m Type
patType ty (PatId name) = do
  modify . M.insert name $ Base ty
  return ty
patType ty (PatCon conName args) = do
  conTy <- lookupId conName
  case conArgTypes conTy of
    Just (retTy,argTys) -> do
      let argsLen = length args
          argTysLen = length argTys
      when (length args /= length argTys) . throwError $ PatternArgMismatch argsLen argTysLen
      for_ (zip args argTys) $ \(arg,argTy) -> do
        ctxt <- get
        modify . M.insert arg $ case argTy of
          TypeVar{} -> Base . TypeVar . fresh $ free ctxt `S.union` boundInContext ctxt
          _ -> Base argTy
      ctxt <- get
      instantiate . generalize ctxt <$> unify ty retTy
    Nothing -> error "Cannot determine data constructor arguments"
patType ty (PatLit (LitInt p)) = unify ty $ PrimType Int
patType ty (PatLit (LitString p)) = unify ty $ PrimType String
patType ty (PatLit (LitChar p)) = unify ty $ PrimType Char
patType ty (PatLit (LitBool p)) = unify ty $ PrimType Bool

data Literal = LitInt Int
             | LitString String
             | LitChar Char
             | LitBool Bool
             deriving (Eq, Show)

-- Syntax of expressions
data Expr
  = Id Identifier
  | Lit Literal
  | App Expr Expr
  | Abs Identifier Expr
  | Let Identifier Expr Expr
  | Case Expr [(Pattern,Expr)]
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
  | PolyType String [Type]
  deriving (Eq, Show, Ord)

-- Syntax of type schemes
data TypeScheme
  = Base Type
  | Forall String TypeScheme
  deriving (Eq, Show, Ord)

freeInType :: Type -> Set Identifier
freeInType (TypeVar name) = S.singleton name
freeInType (FunType from to) = freeInType from `S.union` freeInType to
freeInType _ = S.empty

freeInScheme :: TypeScheme -> Set Identifier
freeInScheme (Base ty) = freeInType ty
freeInScheme (Forall name scheme)
  = freeInScheme scheme `S.difference` S.singleton name

type Context = Map Identifier TypeScheme

free :: Context -> Set Identifier
free
  = foldl (\frees (name,ty) -> frees `S.union` freeInScheme ty) S.empty . M.toList

bound :: TypeScheme -> (Type, Set Identifier)
bound (Base ty) = (ty, S.empty)
bound (Forall name scheme) = S.insert name <$> bound scheme

boundInContext :: Context -> Set Identifier
boundInContext
  = foldl (\bounds (name,ty) -> bounds `S.union` snd (bound ty)) S.empty . M.toList

type Substitutions = Map Identifier Type

specializeTypes :: Set Identifier -> Type -> Type -> Bool
specializeTypes names ty ty'
  = evalState (canSpecialize names ty ty') M.empty
  where
    canSpecializeMulti names a a' b b'
      = liftA2 (&&) (canSpecialize names a a') (canSpecialize names b b')

    canSpecialize :: Set Identifier -> Type -> Type -> State Substitutions Bool
    canSpecialize names (TypeVar name) ty' = do
      sub <- gets $ M.lookup name
      case sub of
        Just ty -> return $ ty == ty'
        Nothing -> do
          let nameInNames = name `S.member` names
          when nameInNames . modify $ M.insert name ty'
          return nameInNames
    canSpecialize names ty@PrimType{} ty' = return $ ty == ty'
    canSpecialize names (FunType from to) (FunType from' to')
      = canSpecializeMulti names from from' to to'
    canSpecialize names (PolyType tyName tys) (PolyType tyName' tys')
      = fmap (tyName == tyName' &&)
        getAll . fold <$> traverse (\(a,b) -> All <$> canSpecialize names a b) (zip tys tys')
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

generalize :: Context -> Type -> TypeScheme
generalize ctxt ty
  = foldl
      (flip Forall)
      (Base ty)
      (freeInType ty `S.difference` free ctxt)

substitute :: Substitutions -> Type -> Type
substitute subs ty@(TypeVar name) = fromMaybe ty $ M.lookup name subs
substitute subs (FunType from to) = FunType (substitute subs from) (substitute subs to)
substitute subs (PolyType tyName tys) = PolyType tyName $ map (substitute subs) tys
substitute subs ty = ty

substituteScheme :: Substitutions -> TypeScheme -> TypeScheme
substituteScheme subs (Base ty) = Base $ substitute subs ty
substituteScheme subs (Forall name scheme) = substituteScheme (M.delete name subs) scheme

substituteContext :: Substitutions -> Context -> Context
substituteContext subs = fmap (substituteScheme subs)

fresh :: Set Identifier -> Identifier
fresh exclude = fresh' exclude (fmap pure ['a'..'z']) 0
  where
    fresh' exclude [] n
      = let n' = n + 1 in fresh' exclude (fmap (: show n') ['a'..'z']) n'
    fresh' exclude (x:xs) n
      | x `S.member` exclude = fresh' exclude xs n
      | otherwise = x

instantiate :: TypeScheme -> Type
instantiate (Base ty) = ty
instantiate scheme
  = let (ty,tyVars) = bound scheme
        subs = createSubs tyVars $ freeInScheme scheme
    in substitute subs ty
  where
    createSubs exclude
      = foldl (\acc name ->
          M.insert
            name
            (TypeVar $ fresh (exclude `S.union` M.keysSet acc))
            acc)
          M.empty
                

data InferenceError
  = NotInScope String
  | TypeError Type Type
  | PatternArgMismatch Int Int
  | OccursError Identifier Type
  deriving Show

occurs :: MonadError InferenceError m => Identifier -> Type -> m ()
occurs name ty
  | name `S.member` freeInType ty = throwError $ OccursError name ty
  | otherwise = return ()

unify :: MonadError InferenceError m => Type -> Type -> m Type
unify ty@TypeVar{} TypeVar{} = return ty
unify (TypeVar name) ty = return ty
unify ty (TypeVar name) = return ty
unify (FunType from to) (FunType from' to')
  = liftA2 FunType (unify from from') (unify to to')
unify ty@(PolyType tyName tys) ty'@(PolyType tyName' tys')
  | tyName == tyName' = PolyType tyName <$> traverse (uncurry unify) (zip tys tys')
  | otherwise = throwError $ TypeError ty ty'
unify ty ty'
  | ty == ty' = return ty'
  | otherwise = throwError $ TypeError ty ty'

unionWithError :: (Ord k, MonadError InferenceError m)
               => Map k Type
               -> Map k Type
               -> m (Map k Type)
unionWithError m m'
  = for (M.intersectionWith (,) m m') comparison
  where
    comparison (a,b)
      | a == b = return a
      | otherwise = throwError $ TypeError a b
  

mgu :: MonadError InferenceError m => Type -> Type -> m Substitutions
mgu (TypeVar name) ty = occurs name ty >> return (M.singleton name ty)
mgu ty (TypeVar name) = return $ M.singleton name ty
mgu (FunType from to) (FunType from' to') = do
  fromSubs <- mgu from from'
  toSubs <- mgu (substitute fromSubs to) (substitute fromSubs to')
  return $ M.union fromSubs toSubs
mgu ty@(PolyType tyName tys) ty'@(PolyType tyName' tys')
  | tyName == tyName' = fold <$> traverse (uncurry mgu) (zip tys tys')
  | otherwise = throwError $ TypeError ty ty'
mgu ty ty'
  | ty == ty' = return M.empty
  | otherwise = throwError $ TypeError ty ty'

usingState :: MonadState s m => (s -> s) -> m a -> m a
usingState f s = do
  original <- get
  modify f
  a <- s
  put original
  return a

w :: Expr -> Context -> Either InferenceError TypeScheme
w e ctxt
  = let (res,ctxt') = runState (runExceptT $ w' e) ctxt
    in generalize ctxt' . uncurry substitute <$> res
  where
    w' :: (MonadError InferenceError m, MonadState Context m)
       => Expr
       -> m (Substitutions, Type)
    w' e = case e of
        (Id name) -> do
          res <- gets $ M.lookup name
          case res of
            Nothing -> throwError $ NotInScope name
            Just scheme -> return (M.empty, instantiate scheme)
        (Lit (LitInt e)) -> return (M.empty,PrimType Int)
        (Lit (LitString e)) -> return (M.empty,PrimType String)
        (Lit (LitChar e)) -> return (M.empty,PrimType Char)
        (Lit (LitBool e)) -> return (M.empty,PrimType Bool)
        (App f x) -> do
          (s1,t1) <- w' f
          (s2,t2) <- usingState (substituteContext s1) $ w' x
          ctxt <- get
          let b = TypeVar $ fresh (free ctxt `S.union` boundInContext ctxt)
          s3 <- mgu (substitute s2 t1) (FunType t2 b)
          return (s3 `M.union` s2 `M.union` s1, substitute s3 b)
        (Abs x expr) -> do
          ctxt <- get
          let b = TypeVar $ fresh (free ctxt `S.union` boundInContext ctxt)
          modify $ M.insert x (Base b)
          (s1,t1) <- w' expr 
          put ctxt
          return (s1,substitute s1 $ FunType b t1)
        (Let x e e') -> do
          (s1,t1) <- w' e
          ctxt <- get
          modify $ substituteContext s1
          modify $ M.insert x $ generalize (substituteContext s1 ctxt) t1
          (s2,t2) <- w' e' 
          put ctxt
          return (s2 `M.union` s1, t2)
        (Case e bs) -> do
          (s1,t1) <- w' e
          ts <- for bs $ \(p,b) -> do
            ctxt <- get
            t <- patType t1 p -- Determine type of pattern
            subs <- mgu t1 t -- unify pattern's type with case expr's type
            (s',t') <- w' b -- infer right hand side
            put ctxt
            return (subs,t')
          case ts of
            [] -> error "Case expression cannot have zero branches"
            ((subs,t):ts) -> traverse (unify t . snd) ts >> return (subs,t)
