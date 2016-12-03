{-# language FlexibleContexts #-}

module Lambda where

import Control.Applicative
import Control.Lens
import Control.Monad.Except
import Control.Monad.State
import Data.Bifunctor
import Data.Foldable
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as M
import Data.Monoid ((<>), All(..))
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as N
import Data.Traversable
import Data.Set (Set)
import qualified Data.Set as S

import Lambda.Core

import Debug.Trace

data InferenceState
  = InferenceState
    { _context :: Map Identifier TypeScheme
    , _typeTable :: Map Identifier Int
    , _freshCount :: Int
    }

class HasContext s where
  context :: Lens' s (Map Identifier TypeScheme)

-- Currently the only information stored in this table is the arity of a type
-- contructor
class HasTypeTable s where
  typeTable :: Lens' s (Map Identifier Int)

class HasFreshCount s where
  freshCount :: Lens' s Int

instance HasContext InferenceState where
  context = lens _context (\s c -> s { _context = c })

instance HasTypeTable InferenceState where
  typeTable = lens _typeTable (\s t -> s { _typeTable = t })

instance HasFreshCount InferenceState where
  freshCount = lens _freshCount (\s c -> s { _freshCount = c })

data InferenceError
  = NotInScope [String]
  | TypeError Type Type
  | PatternArgMismatch Int Int
  | OccursError Identifier Type
  | AlreadyDefined Identifier
  | TooManyArguments TypeScheme
  | WrongArity [Type]
  | NotDefined Identifier
  deriving (Eq, Show)

lookupId :: (HasContext s, MonadError InferenceError m, MonadState s m)
         => Identifier
         -> m TypeScheme
lookupId name = do
  maybeTy <- use (context . at name)
  case maybeTy of
    Just ty -> return ty
    Nothing -> throwError $ NotInScope [name]

conArgTypes :: Type -> (Type,[Type])
conArgTypes (FunType from to) = (from :) <$> conArgTypes to
conArgTypes ty = (ty,[])

patType :: (HasContext s, HasFreshCount s, MonadError InferenceError m, MonadState s m)
        => Pattern
        -> m Type
patType (PatCon conName args) = do
  conTy <- instantiate =<< lookupId conName
  let (retTy,argTys) = conArgTypes conTy
      argsLen = length args
      argTysLen = length argTys
  when (argsLen /= argTysLen) . throwError $ PatternArgMismatch argsLen argTysLen
  for_ (zip args argTys) $ \(arg,argTy) -> context %= M.insert arg (Base argTy)
  return retTy
patType (PatLit (LitInt p)) = return $ PrimType Int
patType (PatLit (LitString p)) = return $ PrimType String
patType (PatLit (LitChar p)) = return $ PrimType Char

freeInType :: Type -> Set Identifier
freeInType (TypeVar name) = S.singleton name
freeInType (FunType from to) = freeInType from `S.union` freeInType to
freeInType (PolyType _ args) = foldr (\a b -> freeInType a `S.union` b) S.empty args
freeInType _ = S.empty

freeInScheme :: TypeScheme -> Set Identifier
freeInScheme (Base ty) = freeInType ty
freeInScheme (Forall name scheme)
  = freeInScheme scheme `S.difference` S.singleton name

free :: Map Identifier TypeScheme -> Set Identifier
free
  = foldl (\frees (name,ty) -> frees `S.union` freeInScheme ty) S.empty . M.toList

bound :: TypeScheme -> (Type, Set Identifier)
bound (Base ty) = (ty, S.empty)
bound (Forall name scheme) = S.insert name <$> bound scheme

boundInContext :: Map Identifier TypeScheme -> Set Identifier
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

generalize :: Map Identifier TypeScheme -> Type -> TypeScheme
generalize ctxt ty
  = foldr
      Forall
      (Base ty)
      (freeInType ty `S.difference` free ctxt)

substitute :: Substitutions -> Type -> Type
substitute subs ty@(TypeVar name) = fromMaybe ty $ M.lookup name subs
substitute subs (FunType from to) = FunType (substitute subs from) (substitute subs to)
substitute subs (PolyType tyName tys) = PolyType tyName $ map (substitute subs) tys
substitute subs ty = ty

substituteScheme :: Substitutions -> TypeScheme -> TypeScheme
substituteScheme subs (Base ty) = Base $ substitute subs ty
substituteScheme subs (Forall name scheme) = Forall name $ substituteScheme (M.delete name subs) scheme

substituteContext :: Substitutions -> Map Identifier TypeScheme -> Map Identifier TypeScheme
substituteContext subs = fmap (substituteScheme subs)

fresh :: (HasFreshCount s, MonadState s m) => m Type
fresh = do
  n <- use freshCount
  freshCount += 1
  return . TypeVar $ "t" ++ show n

instantiate :: (HasContext s, HasFreshCount s, MonadState s m) => TypeScheme -> m Type
instantiate (Base ty) = return ty
instantiate scheme = do
  ctxt <- use context
  let (ty,tyVars) = bound scheme
  subs <-  createSubs
    (free ctxt `S.union` boundInContext ctxt `S.union` freeInScheme scheme)
    tyVars
  return $ substitute subs ty
  where
    createSubs exclude
      = foldl (\acc name -> M.insert name <$> fresh <*> acc) (return M.empty)

occurs :: MonadError InferenceError m => Identifier -> Type -> m ()
occurs name ty
  | name `S.member` freeInType ty = throwError $ OccursError name ty
  | otherwise = return ()

mgu :: MonadError InferenceError m => Type -> Type -> m Substitutions
mgu (TypeVar name) ty@TypeVar{} = return (M.singleton name ty)
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

usingState :: MonadState s m => m a -> m a
usingState ma = do
  original <- get
  a <- ma
  put original
  return a

runW :: Expr -> Either InferenceError TypeScheme
runW = runExcept . flip evalStateT (InferenceState M.empty M.empty 0) . w

w :: (HasFreshCount s, HasContext s, MonadError InferenceError m, MonadState s m) => Expr -> m TypeScheme
w e = do
  res <- w' e
  ctxt <- use context
  return . generalize ctxt $ uncurry substitute res
  where
    w' :: (HasContext s, HasFreshCount s, MonadError InferenceError m, MonadState s m)
       => Expr
       -> m (Substitutions, Type)
    w' e = case e of
        (Error _) -> (,) M.empty <$> fresh
        (Id name) -> do
          res <- use (context . at name)
          case res of
            Nothing -> throwError $ NotInScope [name]
            Just scheme -> (,) M.empty <$> instantiate scheme
        (Lit (LitInt e)) -> return (M.empty,PrimType Int)
        (Lit (LitString e)) -> return (M.empty,PrimType String)
        (Lit (LitChar e)) -> return (M.empty,PrimType Char)
        (App f x) -> do
          (s1,t1) <- w' f
          (s2,t2) <- usingState $ do
            context %= substituteContext s1
            w' x
          b <- fresh
          s3 <- mgu (substitute s2 t1) (FunType t2 b)
          return (s3 `M.union` s2 `M.union` s1, substitute s3 b)
        (Abs x expr) -> do
          b <- fresh
          (s1,t1) <- usingState $ do
            context %= M.insert x (Base b)
            w' expr
          return (s1,FunType (substitute s1 b) t1)
        (PatAbs pat expr) -> do
          ty <- patType pat
          (s1,t1) <- w' expr
          return (s1,FunType (substitute s1 ty) t1)
        (Let x e e') -> do
          (s1,t1) <- w' e
          (s2,t2) <- usingState $ do
            context %= substituteContext s1
            ctxt <- use context
            context %= M.insert x (generalize (substituteContext s1 ctxt) t1)
            w' e'
          return (s2 `M.union` s1, t2)
        (Chain e1 e2) -> do
          (s1,t1) <- w' e1
          (s2,t2) <- usingState $ do
            context %= substituteContext s1
            w' e2
          s3 <- mgu t1 t2
          return (s1 `M.union` s2, substitute s3 t1)

buildFunction :: [Type] -> Type -> Type
buildFunction argTys retTy = foldr FunType retTy argTys

-- [_,_,_,_] -> Abs "a1" (Abs "a2" (Abs "a3" (Abs "a4" (Prod name [Id "a1", Id "a2", Id "a3", Id "a4"]))))
-- _:xs -> ([Id "a1"], Abs "a1")
buildDataCon :: Product -> Expr
buildDataCon (Product dataCon argTys)
  = let (args, expr) = go (take (length argTys) (mappend "a" . show <$> [1..]))
    in expr $ Prod dataCon args
  where
    go [] = ([], id)
    go (var:vars) = bimap (Id var :) (Abs var <$>) $ go vars

checkDecl :: (HasFreshCount s, HasTypeTable s, HasContext s, MonadState s m, MonadError InferenceError m) => Definition -> m (Map Identifier Expr)
checkDecl (Data tyCon tyVars decls) = do
  freshCount .= 0
  M.fromList <$> traverse (checkDataDecl tyCon tyVars) (N.toList decls)
  where
    tyVarsNotInScope tyVars argTys =
      foldr S.union S.empty (fmap freeInType argTys) `S.difference` S.fromList tyVars

    arity n (PolyType name as) = do
      maybeArity <- use (typeTable . at name)
      case maybeArity of
        Nothing -> throwError $ NotDefined name
        Just maxArity -> return $ maxArity - length as == n
    arity 0 _ = return True
    arity _ _ = return False

    checkDataDecl tyCon tyVars p@(Product dataCon argTys) = do
      maybeCon <- use (context . at dataCon)
      case maybeCon of
        Just _ -> throwError $ AlreadyDefined dataCon
        Nothing -> do
          let notInScope = tyVarsNotInScope tyVars argTys
          when (notInScope /= S.empty) . throwError . NotInScope $ S.toList notInScope
          typeTable %= M.insert tyCon (length tyVars)
          wrongArities <- filterM (fmap not . arity 0) argTys
          when (wrongArities /= []) . throwError $ WrongArity wrongArities
          let conFun = buildFunction argTys $ PolyType tyCon (fmap TypeVar tyVars)
          subs <- M.fromList . zip tyVars <$> replicateM (length tyVars) fresh
          ctxt <- use context
          context %= M.insert dataCon (generalize ctxt $ substitute subs conFun)
          return (dataCon, buildDataCon p)

checkDecl _ = return M.empty
