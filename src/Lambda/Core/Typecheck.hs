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
import Lambda.Core.Kinds

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

conArgTypes :: Type -> (Type,[Type])
conArgTypes (TyFun from to) = (from :) <$> conArgTypes to
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
freeInScheme (Forall vars ty) = freeInType ty `S.difference` vars

free :: Map Identifier TypeScheme -> Set Identifier
free = foldr (\scheme frees -> freeInScheme scheme `S.union` frees) S.empty

type Substitution = Map Identifier Type

generalize :: Map Identifier TypeScheme -> Type -> TypeScheme
generalize ctxt ty = Forall (freeInType ty `S.difference` free ctxt) ty

substitute :: Substitution -> Type -> Type
substitute subs ty@(TyVar name) = fromMaybe ty $ M.lookup name subs
substitute subs (TyApp from to) = TyApp (substitute subs from) (substitute subs to)
substitute subs ty = ty

-- apply s1 to s2
applySubs :: Substitution -> Substitution -> Substitution
applySubs s1 = M.union s1 . fmap (substitute s1)

subTypeScheme :: Substitution -> TypeScheme -> TypeScheme
subTypeScheme subs (Base ty) = Base $ substitute subs ty
subTypeScheme subs (Forall vars ty) = Forall vars $ substitute (foldr M.delete subs vars) ty

subContext :: Substitution -> Map Identifier TypeScheme -> Map Identifier TypeScheme
subContext subs = fmap (subTypeScheme subs)

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
instantiate (Forall vars ty) = do
  subs <- M.fromList <$> for (S.toList vars) (\var -> (,) var <$> fresh)
  pure $ substitute subs ty

occurs :: Identifier -> Type -> Bool
occurs name ty = name `S.member` freeInType ty

mgu :: (AsTypeError e, MonadError e m) => Constraint -> m Substitution
mgu [] = pure M.empty
mgu (eq:eqs)
  | uncurry (==) eq = mgu eqs
  | otherwise = case eq of
      (TyVar name,ty)
        | not $ occurs name ty -> do
            let sub = M.singleton name ty
            subs <- mgu $ substituteConstraint sub eqs
            pure $ applySubs sub subs
        | otherwise -> throwError $ _OccursError # (name,ty)
      (ty,TyVar name) -> mgu $ (TyVar name,ty):eqs
      (TyApp con arg,TyApp con' arg') -> mgu $ (con,con'):(arg,arg'):eqs
      (ty,ty') -> throwError $ _TypeMismatch # (ty,ty')

unify :: (AsTypeError e, MonadError e m) => TypeScheme -> TypeScheme -> m ()
unify scheme scheme'
  | scheme == scheme' = pure ()
  | otherwise = case (scheme,scheme') of
      (Forall vars ty,Forall vars' ty')
        | vars == vars' -> unifyTypes ty ty'
        | otherwise -> do
            let subs = M.fromList $ zip (S.elems vars) (S.elems vars')
            let bound = S.difference vars vars' `S.union` vars'
            unify (Forall bound $ substitute (TyVar <$> subs) ty) (Forall bound ty')
      (Forall vars ty,Base ty') -> unifyTypes ty ty'
      (Base ty,Base ty') -> unifyTypes ty ty'
      _ -> unify scheme' scheme
  where
    unifyTypes (TyApp con arg) (TyApp con' arg') = unifyTypes arg arg' >> unifyTypes con con'
    unifyTypes ty ty'
      | ty == ty' = pure ()
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
  (subs,ty) <- w' e
  ctxt <- view context
  return . generalize ctxt $ substitute subs ty
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
      -> m (Substitution, [(Type,Type)])
    inferBranches = foldrM inferBranch (M.empty,[])
      where
        inferBranch (pat,branch) (subs,bTypes) = do
          res <- patType pat
          case res of
            Just (boundVars,patternType) ->
              local (over context $ M.union boundVars) $ do
                (branchSubs,branchType) <- w' branch
                pure (applySubs branchSubs subs, (patternType,branchType):bTypes)
            Nothing -> do
              (branchSubs,branchType) <- w' branch
              patternType <- fresh
              pure (applySubs branchSubs subs, (patternType,branchType):bTypes)

    w' ::
      ( HasFreshCount s
      , MonadState s m
      , HasContext r
      , MonadReader r m
      , AsTypeError e
      , MonadError e m
      )
      => Expr
      -> m (Substitution, Type)
    w' e = case e of
        (Error _) -> (,) M.empty <$> fresh
        (Id name) -> do
          res <- view (context . at name)
          case res of
            Nothing -> throwError $ _NotInScope # [name]
            Just scheme -> (,) M.empty <$> instantiate scheme
        (Lit (LitInt e)) -> return (M.empty,TyPrim Int)
        (Lit (LitString e)) -> return (M.empty,TyPrim String)
        (Lit (LitChar e)) -> return (M.empty,TyPrim Char)
        (Lit (LitBool e)) -> return (M.empty,TyPrim Bool)
        (App f x) -> do
          (s1,t1) <- w' f
          (s2,t2) <- local (over context $ subContext s1) $ w' x
          b <- fresh
          s3 <- mgu [(TyFun t2 b,substitute s2 t1)]
          return (applySubs s3 $ applySubs s2 s1, substitute s3 b)
        (Abs x expr) -> do
          ctxt <- get
          b <- fresh
          (s1,t1) <- local (over context $ M.insert x (Base b)) $ w' expr
          return (s1,TyFun (substitute s1 b) t1)
        (Let (Binding x e) e') -> do
          (s1,t1) <- w' e
          let addVar ctxt = let ctxt' = subContext s1 ctxt in M.insert x (generalize ctxt' t1) ctxt'
          (s2,t2) <- local (over context addVar) $ w' e'
          return (applySubs s2 s1, t2)
        (Rec (Binding name value) rest) -> do
          freshVar <- fresh
          (s1,t1) <- local (over context . M.insert name $ Base freshVar) $ w' value
          s2 <- mgu $ (t1,freshVar) : M.toList (M.mapKeys TyVar s1)
          (s3,t2) <- local (over context $ \ctxt -> M.insert name (generalize ctxt $ substitute s2 t1) $ subContext s1 ctxt) $ w' rest
          pure (applySubs s3 s1,t2)
        (Case input bs) -> do
          (s1,inputType) <- w' input
          (bSubs,bs') <- inferBranches bs
          outputType <- fresh
          let constraints = foldr (\(p,b) constrs -> (p,inputType):(b,outputType):constrs) [] bs'
          subs <- mgu constraints
          pure (applySubs subs $ applySubs bSubs s1,substitute subs outputType)

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
          let conFun = flip (foldr TyFun) argTys $ foldl' TyApp (TyCon $ TypeCon tyCon) tyVars
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
      case ty of
        Forall vars ty -> validateType vars ty
        Base ty -> validateType S.empty ty
      typesignatures %= M.insert name ty
    _ -> throwError $ _DuplicateTypeSignatures # name
  pure M.empty
  where
    validateType bound (TyVar ty) = unless (ty `S.member` bound) . throwError $ _FreeTyVar # ty
    validateType bound ty = do
      table <- use kindTable
      void . flip runStateT (KindInferenceState 0) $ do
        bound' <- for (S.toList bound) $ \a -> (,) a <$> freshKindVar
        flip runReaderT (M.fromList bound' `M.union` table) $ inferKind ty

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
