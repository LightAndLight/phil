{-# LANGUAGE TemplateHaskell       #-}

module Lambda.Core.Typecheck where

import           Control.Applicative
import           Control.Lens
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State
import           Data.Foldable
import           Data.List.NonEmpty   (NonEmpty (..))
import qualified Data.List.NonEmpty   as N
import           Data.Map             (Map)
import qualified Data.Map             as M
import           Data.Maybe
import           Data.Monoid
import           Data.Set             (Set)
import qualified Data.Set             as S
import           Data.Traversable

import           Lambda.Core.AST

data InferenceState
  = InferenceState
    { _context    :: Map Identifier TypeScheme
    , _typeTable  :: Map Identifier Int
    , _freshCount :: Int
    }

initialInferenceState = InferenceState M.empty M.empty 0

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

data TypeError
  = NotInScope [String]
  | TypeMismatch Type Type
  | PatternArgMismatch Int Int
  | OccursError Identifier Type
  | AlreadyDefined Identifier
  | TooManyArguments TypeScheme
  | WrongArity [Type]
  | NotDefined Identifier
  deriving (Eq, Show)

makeClassyPrisms ''TypeError

lookupId ::
  ( HasContext r
  , MonadReader r m
  , AsTypeError e
  , MonadError e m
  )
  => Identifier
  -> m TypeScheme
lookupId name = do
  maybeTy <- view (context . at name)
  case maybeTy of
    Just ty -> return ty
    Nothing -> throwError $ _NotInScope # [name]

conArgTypes :: Type -> (Type,[Type])
conArgTypes (FunType from to) = (from :) <$> conArgTypes to
conArgTypes ty = (ty,[])

patType ::
  ( HasFreshCount s
  , MonadState s m
  , HasContext r
  , MonadReader r m
  , AsTypeError e
  , MonadError e m
  )
  => Pattern
  -> m (Map Identifier TypeScheme,Type)
patType (PatId name) = do
  ty <- fresh
  return (M.singleton name $ Base ty,ty)
patType (PatCon conName args) = do
  conTy <- instantiate =<< lookupId conName
  let (retTy,argTys) = conArgTypes conTy
      argsLen = length args
      argTysLen = length argTys
  when (argsLen /= argTysLen) . throwError $ _PatternArgMismatch # (argsLen,argTysLen)
  let boundVars = foldr (\(arg,argTy) -> M.insert arg (Base argTy)) M.empty $ zip args argTys
  return (boundVars,retTy)
patType (PatLit (LitInt p)) = return (M.empty,PrimType Int)
patType (PatLit (LitString p)) = return (M.empty,PrimType String)
patType (PatLit (LitChar p)) = return (M.empty,PrimType Char)

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

instantiate ::
  ( HasFreshCount s
  , MonadState s m
  , HasContext r
  , MonadReader r m
  )
  => TypeScheme
  -> m Type
instantiate (Base ty) = return ty
instantiate scheme = do
  ctxt <- view context
  let (ty,tyVars) = bound scheme
  subs <- createSubs
    (free ctxt `S.union` boundInContext ctxt `S.union` freeInScheme scheme)
    tyVars
  return $ substitute subs ty
  where
    createSubs exclude
      = foldl (\acc name -> M.insert name <$> fresh <*> acc) (return M.empty)


occurs :: (AsTypeError e, MonadError e m) => Identifier -> Type -> m ()
occurs name ty
  | name `S.member` freeInType ty = throwError $ _OccursError # (name,ty)
  | otherwise = return ()

mgu :: (AsTypeError e, MonadError e m) => Type -> Type -> m Substitutions
mgu (TypeVar name) ty@TypeVar{} = return (M.singleton name ty)
mgu (TypeVar name) ty = occurs name ty >> return (M.singleton name ty)
mgu ty (TypeVar name) = return $ M.singleton name ty
mgu (FunType from to) (FunType from' to') = do
  fromSubs <- mgu from from'
  toSubs <- mgu (substitute fromSubs to) (substitute fromSubs to')
  return $ M.union fromSubs toSubs
mgu ty@(PolyType tyName tys) ty'@(PolyType tyName' tys')
  | tyName == tyName' = fold <$> traverse (uncurry mgu) (zip tys tys')
  | otherwise = throwError $ _TypeMismatch # (ty,ty')
mgu ty ty'
  | ty == ty' = return M.empty
  | otherwise = throwError $ _TypeMismatch # (ty,ty')

runW :: Expr -> Either TypeError TypeScheme
runW = runExcept . flip evalStateT initialInferenceState . flip runReaderT initialInferenceState . w

runWithContext :: (AsTypeError e, MonadError e m) => Map Identifier TypeScheme -> Expr -> m TypeScheme
runWithContext ctxt
  = flip evalStateT initialInferenceState .
    flip runReaderT initialInferenceState { _context = ctxt } . w

w ::
  ( HasFreshCount s
  , MonadState s m
  , HasContext r
  , MonadReader r m
  , AsTypeError e
  , MonadError e m
  )
  => Expr
  -> m TypeScheme
w e = do
  res <- w' e
  ctxt <- view context
  return . generalize ctxt $ uncurry substitute res
  where
    w' ::
      ( HasFreshCount s
      , MonadState s m
      , HasContext r
      , MonadReader r m
      , AsTypeError e
      , MonadError e m
      )
      => Expr
      -> m (Substitutions, Type)
    w' e = case e of
        (Error _) -> (,) M.empty <$> fresh
        (Id name) -> do
          res <- view (context . at name)
          case res of
            Nothing -> throwError $ _NotInScope # [name]
            Just scheme -> (,) M.empty <$> instantiate scheme
        (Lit (LitInt e)) -> return (M.empty,PrimType Int)
        (Lit (LitString e)) -> return (M.empty,PrimType String)
        (Lit (LitChar e)) -> return (M.empty,PrimType Char)
        (App f x) -> do
          (s1,t1) <- w' f
          local (over context $ substituteContext s1) $ do
            (s2,t2) <- w' x
            b <- fresh
            s3 <- mgu (substitute s2 t1) (FunType t2 b)
            return (s3 `M.union` s2 `M.union` s1, substitute s3 b)
        (Abs x expr) -> do
          ctxt <- get
          b <- fresh
          local (over context $ M.insert x (Base b)) $ do
            (s1,t1) <- w' expr
            return (s1,FunType (substitute s1 b) t1)
        (Let x e e') -> do
          (s1,t1) <- w' e
          ctxt <- view context
          let addVar = M.insert x (generalize (substituteContext s1 ctxt) t1) . substituteContext s1
          local (over context addVar) $ do
            (s2,t2) <- w' e'
            return (s2 `M.union` s1, t2)
        (Case e bs) -> do
          ((pt',bt') :| bs') <- for bs $ \(p,b) -> do
            (boundVars,pt) <- patType p
            local (over context $ M.union boundVars) $ do
              (_,bt) <- w' b
              return (pt,bt)
          let foldOver (pt,_) m = do
                (subs,t) <- m
                subs' <- mgu pt t
                return (subs `M.union` subs', substitute subs' pt)
          (subslhs,tlhs) <- foldr foldOver (return (M.empty, pt')) bs'
          let trhs = substitute subslhs bt'
          subsrhs <- foldr (\(_,bt) subs -> liftA2 M.union (mgu (substitute subslhs bt) trhs) subs) (return M.empty) bs'
          let t'lhs = substitute subsrhs tlhs
          (_,te) <- w' e
          liftA2 (,) (mgu te t'lhs) (pure trhs)

buildFunction :: [Type] -> Type -> Type
buildFunction argTys retTy = foldr FunType retTy argTys

-- [_,_,_,_] -> Abs "a1" (Abs "a2" (Abs "a3" (Abs "a4" (Prod name [Id "a1", Id "a2", Id "a3", Id "a4"]))))
-- _:xs -> ([Id "a1"], Abs "a1")
buildDataCon :: ProdDecl -> Expr
buildDataCon (ProdDecl dataCon argTys)
  = let (args, expr) = go (take (length argTys) (mappend "a" . show <$> [1..]))
    in expr $ Prod dataCon args
  where
    go [] = ([], id)
    go (var:vars) = bimap (Id var :) (Abs var <$>) $ go vars

checkDefinition ::
  ( HasFreshCount s
  , HasTypeTable s
  , HasContext s
  , MonadState s m
  , AsTypeError e
  , MonadError e m
  )
  => Definition
  -> m (Map Identifier Expr)
checkDefinition (Data tyCon tyVars decls) = do
  freshCount .= 0
  M.fromList <$> traverse (checkDataDecl tyCon tyVars) (N.toList decls)
  where
    tyVarsNotInScope tyVars argTys =
      foldr S.union S.empty (fmap freeInType argTys) `S.difference` S.fromList tyVars

    arity n (PolyType name as) = do
      maybeArity <- use (typeTable . at name)
      case maybeArity of
        Nothing -> throwError $ _NotDefined # name
        Just maxArity -> return $ maxArity - length as == n
    arity 0 _ = return True
    arity _ _ = return False

    checkDataDecl tyCon tyVars p@(ProdDecl dataCon argTys) = do
      maybeCon <- use (context . at dataCon)
      case maybeCon of
        Just _ -> throwError $ _AlreadyDefined # dataCon
        Nothing -> do
          let notInScope = tyVarsNotInScope tyVars argTys
          when (notInScope /= S.empty) . throwError $ _NotInScope # S.toList notInScope
          typeTable %= M.insert tyCon (length tyVars)
          wrongArities <- filterM (fmap not . arity 0) argTys
          when (wrongArities /= []) . throwError $ _WrongArity # wrongArities
          let conFun = buildFunction argTys $ PolyType tyCon (fmap TypeVar tyVars)
          subs <- M.fromList . zip tyVars <$> replicateM (length tyVars) fresh
          ctxt <- use context
          context %= M.insert dataCon (generalize ctxt $ substitute subs conFun)
          return (dataCon, buildDataCon p)

checkDefinition (Binding name expr) = do
  freshCount .= 0
  maybeVar <- uses typeTable (M.lookup name)
  case maybeVar of
    Nothing -> do
      ctxt <- use context
      ty <- runWithContext ctxt expr
      context %= M.insert name ty
      return $ M.singleton name expr
    _ -> throwError $ _AlreadyDefined # name

checkDefinitions ::
  ( HasFreshCount s
  , HasTypeTable s
  , HasContext s
  , MonadState s m
  , AsTypeError e
  , MonadError e m
  )
  => [Definition]
  -> m [Definition]
checkDefinitions defs = traverse_ checkDefinition defs *> pure defs
