{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE FlexibleContexts       #-}

module Lambda.Core.Typecheck where

import           Control.Applicative
import Control.Arrow ((***))
import           Control.Lens
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State
import Data.Bifunctor
import           Data.Foldable
import Data.List
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
import Lambda.Core.Kind

import Debug.Trace

data InferenceState
  = InferenceState
    { _context    :: Map Identifier TypeScheme
    , _typesignatures :: Map Identifier TypeScheme
    , _kindTable  :: Map Identifier Kind
    , _freshCount :: Int
    }

initialInferenceState = InferenceState M.empty M.empty M.empty 0

class HasContext s where
  context :: Lens' s (Map Identifier TypeScheme)

class HasTypesignatures s where
  typesignatures :: Lens' s (Map Identifier TypeScheme)

class HasFreshCount s where
  freshCount :: Lens' s Int

class HasKindTable s where
  kindTable :: Lens' s (Map Identifier Kind)

instance HasContext InferenceState where
  context = lens _context (\s c -> s { _context = c })

instance HasTypesignatures InferenceState where
  typesignatures = lens _typesignatures (\s c -> s { _typesignatures = c })

instance HasKindTable InferenceState where
  kindTable = lens _kindTable (\s t -> s { _kindTable = t })

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
  | DuplicateTypeSignatures Identifier
  | FreeTyVar Identifier
  | KindInferenceError KindError
  deriving (Eq, Show)

makeClassyPrisms ''TypeError

instance AsKindError TypeError where
  _KindError = _KindInferenceError . _KindError

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

funTy :: Type -> Type -> Type
funTy a = TyApp (TyApp (TyCon FunTy) a)

conArgTypes :: Type -> (Type,[Type])
conArgTypes (TyApp (TyApp (TyCon FunTy) from) to) = (from :) <$> conArgTypes to
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
  -> m (Maybe (Map Identifier TypeScheme,Type))
patType (PatId name) = do
  ty <- fresh
  return $ Just (M.singleton name $ Base ty,ty)
patType (PatCon conName args) = do
  conTy <- instantiate =<< lookupId conName
  let (retTy,argTys) = conArgTypes conTy
      argsLen = length args
      argTysLen = length argTys
  when (argsLen /= argTysLen) . throwError $ _PatternArgMismatch # (argsLen,argTysLen)
  let boundVars = foldr (\(arg,argTy) -> M.insert arg (Base argTy)) M.empty $ zip args argTys
  return $ Just (boundVars,retTy)
patType (PatLit (LitInt p)) = return $ Just (M.empty,TyPrim Int)
patType (PatLit (LitString p)) = return $ Just (M.empty,TyPrim String)
patType (PatLit (LitChar p)) = return $ Just (M.empty,TyPrim Char)
patType (PatLit (LitBool p)) = return $ Just (M.empty,TyPrim Bool)
patType PatWildcard = return Nothing

freeInType :: Type -> Set Identifier
freeInType (TyVar name) = S.singleton name
freeInType (TyApp con arg) = freeInType con `S.union` freeInType arg
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

type Substitution = Map Identifier Type

specializeTypes :: Set Identifier -> Type -> Type -> Bool
specializeTypes names ty ty'
  = evalState (canSpecialize names ty ty') M.empty
  where
    canSpecializeMulti names a a' b b'
      = liftA2 (&&) (canSpecialize names a a') (canSpecialize names b b')

    canSpecialize :: Set Identifier -> Type -> Type -> State Substitution Bool
    canSpecialize names (TyVar name) ty' = do
      sub <- gets $ M.lookup name
      case sub of
        Just ty -> return $ ty == ty'
        Nothing -> do
          let nameInNames = name `S.member` names
          when nameInNames . modify $ M.insert name ty'
          return nameInNames
    canSpecialize names ty@TyPrim{} ty' = return $ ty == ty'
    canSpecialize names (TyApp from to) (TyApp from' to')
      = canSpecializeMulti names from from' to to'
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

substitute :: Substitution -> Type -> Type
substitute subs ty@(TyVar name) = fromMaybe ty $ M.lookup name subs
substitute subs (TyApp from to) = TyApp (substitute subs from) (substitute subs to)
substitute subs ty = ty

substituteScheme :: Substitution -> TypeScheme -> TypeScheme
substituteScheme subs (Base ty) = Base $ substitute subs ty
substituteScheme subs (Forall name scheme) = Forall name $ substituteScheme (M.delete name subs) scheme

substituteContext :: Substitution -> Map Identifier TypeScheme -> Map Identifier TypeScheme
substituteContext subs = fmap (substituteScheme subs)

type Constraint = [(Type,Type)]

substituteConstraint :: Substitution -> Constraint -> Constraint
substituteConstraint subs = fmap (substitute subs *** substitute subs)

fresh :: (HasFreshCount s, MonadState s m) => m Type
fresh = do
  n <- use freshCount
  freshCount += 1
  return . TyVar $ "t" ++ show n

instantiate ::
  ( HasFreshCount s
  , MonadState s m
  , HasContext r
  , MonadReader r m
  )
  => TypeScheme
  -> m Type
instantiate (Base ty) = return ty
instantiate scheme = instantiate' scheme M.empty
  where
    instantiate' (Base ty) subs = pure $ substitute subs ty
    instantiate' (Forall name ty) subs = do
      freshVar <- fresh
      instantiate' ty $ M.insert name freshVar subs

occurs :: (AsTypeError e, MonadError e m) => Identifier -> Type -> m ()
occurs name ty
  | name `S.member` freeInType ty = throwError $ _OccursError # (name,ty)
  | otherwise = return ()

-- If both arguments are type variables then replaces the first with the second
mgu :: (AsTypeError e, MonadError e m) => Constraint -> m [Substitution]
mgu [] = pure []
mgu ((ty,ty'):c) = mgu1 ty ty' c
  where
    mgu1 ty ty' c
      | ty == ty' = mgu c
      | otherwise = mgu2 ty ty' c

    mgu2 (TyVar name) ty c = do
      occurs name ty
      second <- mgu (substituteConstraint (M.singleton name ty) c)
      pure $ second ++ [M.singleton name ty]
    mgu2 ty (TyVar name) c = mgu2 (TyVar name) ty c
    mgu2 ty@(TyApp from to) ty'@(TyApp from' to') c = mgu ((from,from'):(to,to'):c)
    mgu2 ty ty' c = throwError $ _TypeMismatch # (ty,ty')

unify :: (AsTypeError e, MonadError e m) => TypeScheme -> TypeScheme -> m ()
unify (Base ty) (Base ty') = evalStateT (unifyBase ty ty') M.empty
  where
    unifyBase ty@(TyVar name) ty'@(TyVar name') = do
      maybeTy <- gets $ M.lookup name
      case maybeTy of
        Nothing -> modify $ M.insert name ty'
        Just ty -> when (ty /= ty') . throwError $ _TypeMismatch # (ty,ty')
      maybeTy <- gets $ M.lookup name'
      case maybeTy of
        Nothing -> modify $ M.insert name' ty
        Just ty' -> when (ty /= ty') . throwError $ _TypeMismatch # (ty,ty')
    unifyBase (TyVar name) ty' = do
      maybeTy <- gets $ M.lookup name
      case maybeTy of
        Nothing -> modify $ M.insert name ty'
        Just ty -> when (ty /= ty') . throwError $ _TypeMismatch # (ty,ty')
    unifyBase ty (TyVar name) = do
      maybeTy <- gets $ M.lookup name
      case maybeTy of
        Nothing -> modify $ M.insert name ty
        Just ty' -> when (ty /= ty') . throwError $ _TypeMismatch # (ty,ty')
    unifyBase ty@(TyApp from to) ty'@(TyApp from' to') = do
      unifyBase from from'
      unifyBase to to'
    unifyBase ty ty' = when (ty /= ty') . throwError $ _TypeMismatch # (ty,ty')
unify (Forall a ty) ty' = unify ty ty'
unify ty (Forall a ty') = unify ty ty'

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
  (subs,ty) <- w' e
  ctxt <- view context
  return . generalize ctxt $ foldr substitute ty subs
  where
    inferBranches ::
      ( HasFreshCount s
      , MonadState s m
      , HasContext r
      , MonadReader r m
      , AsTypeError e
      , MonadError e m
      )
      => NonEmpty (Pattern,Expr)
      -> m ([Substitution], [(Type,Type)])
    inferBranches = foldrM inferBranch ([],[])
      where
        inferBranch (pat,branch) (subs,bTypes) = do
          res <- patType pat
          case res of
            Just (boundVars,patternType) ->
              local (over context $ M.union boundVars) $ do
                (branchSubs,branchType) <- w' branch
                pure (branchSubs ++ subs, (patternType,branchType):bTypes)
            Nothing -> do
              (branchSubs,branchType) <- w' branch
              patternType <- fresh
              pure (branchSubs ++ subs, (patternType,branchType):bTypes)

    w' ::
      ( HasFreshCount s
      , MonadState s m
      , HasContext r
      , MonadReader r m
      , AsTypeError e
      , MonadError e m
      )
      => Expr
      -> m ([Substitution], Type)
    w' e = case e of
        (Error _) -> (,) [] <$> fresh
        (Id name) -> do
          res <- view (context . at name)
          case res of
            Nothing -> throwError $ _NotInScope # [name]
            Just scheme -> (,) [] <$> instantiate scheme
        (Lit (LitInt e)) -> return ([],TyPrim Int)
        (Lit (LitString e)) -> return ([],TyPrim String)
        (Lit (LitChar e)) -> return ([],TyPrim Char)
        (Lit (LitBool e)) -> return ([],TyPrim Bool)
        (App f x) -> do
          (s1,t1) <- w' f
          (s2,t2) <- local (over context $ flip (foldr substituteContext) s1) $ w' x
          b <- fresh
          s3 <- mgu [(funTy t2 b,foldr substitute t1 s2)]
          return (s3 ++ s2 ++ s1, foldr substitute b s3)
        (Abs x expr) -> do
          ctxt <- get
          b <- fresh
          (s1,t1) <- local (over context $ M.insert x (Base b)) $ w' expr
          return (s1,funTy (foldr substitute b s1) t1)
        (Let (Binding x e) e') -> do
          (s1,t1) <- w' e
          let addVar ctxt = let ctxt' = foldr substituteContext ctxt s1 in M.insert x (generalize ctxt' t1) ctxt'
          (s2,t2) <- local (over context addVar) $ w' e'
          return (s2 ++ s1, t2)
        (Rec (Binding name value) rest) -> do
          freshVar <- fresh
          (s1,t1) <- local (over context . M.insert name $ Base freshVar) $ w' value
          s2 <- mgu $ (t1,freshVar) : M.toList (M.mapKeys TyVar $ foldr M.union M.empty s1)
          (s3,t2) <- local (over context $ \ctxt -> M.insert name (generalize ctxt $ foldr substitute t1 s2) $ foldr substituteContext ctxt s1) $ w' rest
          pure (s3 ++ s1,t2)
        (Case input bs) -> do
          (s1,inputType) <- w' input
          (bSubs,bs') <- inferBranches bs
          outputType <- fresh
          let constraints = foldr (\(p,b) constrs -> (p,inputType):(b,outputType):constrs) [] bs'
          subs <- mgu constraints
          pure (subs ++ bSubs ++ s1,foldr substitute outputType subs)

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
  , HasKindTable s
  , HasContext s
  , HasTypesignatures s
  , MonadState s m
  , AsTypeError e
  , AsKindError e
  , MonadError e m
  )
  => Definition
  -> m (Map Identifier Expr)
checkDefinition (Data tyCon tyVars decls) = do
  freshCount .= 0
  table <- use kindTable
  kind <- runReaderT (checkDefinitionKinds tyCon tyVars decls) table
  kindTable %= M.insert tyCon kind
  let tyVars' = fmap TyVar tyVars
  M.fromList <$> traverse (checkDataDecl tyCon tyVars') (N.toList decls)
  where
    checkDataDecl tyCon tyVars p@(ProdDecl dataCon argTys) = do
      maybeCon <- use (context . at dataCon)
      case maybeCon of
        Just _ -> throwError $ _AlreadyDefined # dataCon
        Nothing -> do
          let conFun = flip (foldr funTy) argTys $ foldl' TyApp (TyCon $ DataTy tyCon) tyVars
          ctxt <- use context
          context %= M.insert dataCon (generalize ctxt conFun)
          return (dataCon, buildDataCon p)

checkDefinition (Function (Binding name expr)) = do
  freshCount .= 0
  maybeVar <- uses kindTable (M.lookup name)
  case maybeVar of
    Nothing -> do
      ctxt <- use context
      ty <- runWithContext ctxt expr
      maybeSig <- use (typesignatures . at name)
      case maybeSig of
        Nothing -> pure ()
        Just expected -> unify ty expected
      context %= M.insert name ty
      return $ M.singleton name expr
    _ -> throwError $ _AlreadyDefined # name

checkDefinition (TypeSignature name ty) = do
  maybeSig <- use (typesignatures . at name)
  case maybeSig of
    Nothing -> do
      runReaderT (validateSig ty) S.empty
      typesignatures %= M.insert name ty
    _ -> throwError $ _DuplicateTypeSignatures # name
  pure M.empty
  where
    validateSig (Forall name ty) = local (S.insert name) $ validateSig ty
    validateSig (Base ty) = validateType ty

    validateType (TyVar ty) = do
      bound <- ask
      unless (ty `S.member` bound) . throwError $ _FreeTyVar # ty
    validateType ty = do
      table <- use kindTable
      quantified <- ask
      void . flip runStateT (KindInferenceState 0) $ do
        quantified' <- for (S.toList quantified) $ \a -> (,) a <$> freshKindVar
        flip runReaderT (M.fromList quantified' `M.union` table) $ inferKind ty

checkDefinitions ::
  ( HasFreshCount s
  , HasKindTable s
  , HasContext s
  , HasTypesignatures s
  , MonadState s m
  , AsTypeError e
  , AsKindError e
  , MonadError e m
  )
  => [Definition]
  -> m [Definition]
checkDefinitions defs
  = let (dataDefs,rest) = partition isDataDef defs
        (typeSigs,bindings) = partition isTypeSignature rest
    in do
      traverse_ checkDefinition dataDefs
      traverse_ checkDefinition typeSigs
      traverse_ checkDefinition bindings *> pure (dataDefs ++ bindings)
  where
    isTypeSignature TypeSignature{} = True
    isTypeSignature _ = False

    isDataDef Data{} = True
    isDataDef _ = False
