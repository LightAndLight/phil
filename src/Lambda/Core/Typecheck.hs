{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE ConstraintKinds       #-}
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
import           Lambda.Core.AST.Lens
import qualified Lambda.Core.Kinds as K (HasFreshCount(..))
import Lambda.Core.Kinds hiding (HasFreshCount(..))

import Debug.Trace

data InferenceState
  = InferenceState
    { _context    :: Map Identifier TypeScheme
    , _typesignatures :: Map Identifier TypeScheme
    , _kindTable  :: Map Identifier Kind
    , _kindInferenceState :: KindInferenceState
    , _freshCount :: Int
    }

initialInferenceState
  = InferenceState
  { _context = M.empty
  , _typesignatures = M.empty
  , _kindTable = M.empty
  , _kindInferenceState = initialKindInferenceState
  , _freshCount = 0
  }

class HasContext s where
  context :: Lens' s (Map Identifier TypeScheme)

class HasTypesignatures s where
  typesignatures :: Lens' s (Map Identifier TypeScheme)

class HasFreshCount s where
  freshCount :: Lens' s Int

instance HasContext InferenceState where
  context = lens _context (\s c -> s { _context = c })

instance HasTypesignatures InferenceState where
  typesignatures = lens _typesignatures (\s c -> s { _typesignatures = c })

instance HasKindTable InferenceState where
  kindTable = lens _kindTable (\s t -> s { _kindTable = t })

instance HasFreshCount InferenceState where
  freshCount = lens _freshCount (\s c -> s { _freshCount = c })

instance HasKindInferenceState InferenceState where
  kindInferenceState = lens _kindInferenceState (\s c -> s { _kindInferenceState = c })

instance K.HasFreshCount InferenceState where
  freshCount = kindInferenceState . K.freshCount

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
  | KindInferenceError KindError
  | NoInstanceFound Type Type
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

freeInType :: Type -> Set Identifier
freeInType (TyVar name) = S.singleton name
freeInType (TyApp con arg) = freeInType con `S.union` freeInType arg
freeInType _ = S.empty

freeInScheme :: TypeScheme -> Set Identifier
freeInScheme (Base ty) = freeInType ty
freeInScheme (Forall vars _ ty) = freeInType ty `S.difference` vars

free :: Map Identifier TypeScheme -> Set Identifier
free = foldr (\scheme frees -> freeInScheme scheme `S.union` frees) S.empty

type Substitution = Map Identifier Type

generalize :: Map Identifier TypeScheme -> (Set Type, Type) -> TypeScheme
generalize ctxt (cons,ty)
  | let frees = freeInType ty
  , frees /= S.empty = Forall ((frees `S.union` foldr (\el set -> freeInType el `S.union` set) S.empty cons) `S.difference` free ctxt) cons ty
  | otherwise = Base ty

substitute :: Substitution -> Type -> Type
substitute subs ty@(TyVar name) = fromMaybe ty $ M.lookup name subs
substitute subs (TyApp from to) = TyApp (substitute subs from) (substitute subs to)
substitute subs ty = ty

rename :: Map Identifier Type -> TypeScheme -> TypeScheme
rename subs (Forall vars cons ty)
  = Forall
      (S.map (\v -> fromMaybe v (subs ^. at v ^? _Just . _TyVar)) vars)
      (S.map (substitute subs) cons) $
      substitute (M.filterWithKey (\k a -> k `S.member` vars) subs) ty
rename _ (Base ty) = Base ty

-- apply s1 to s2
applySubs :: Substitution -> Substitution -> Substitution
applySubs s1 = M.union s1 . fmap (substitute s1)

subTypeScheme :: Substitution -> TypeScheme -> TypeScheme
subTypeScheme subs (Base ty) = Base $ substitute subs ty
subTypeScheme subs (Forall vars cons ty) = Forall vars cons $ substitute (foldr M.delete subs vars) ty

subContext :: Substitution -> Map Identifier TypeScheme -> Map Identifier TypeScheme
subContext subs = fmap (subTypeScheme subs)

type Constraints = [(Type,Type)]

substituteConstraint :: Substitution -> Constraints -> Constraints
substituteConstraint subs = fmap (substitute subs *** substitute subs)

fresh :: (HasFreshCount s, HasKindTable s, K.HasFreshCount s, MonadState s m) => m Type
fresh = do
  n <- use freshCount
  freshCount += 1
  let name = "t" ++ show n
  updateKindTable <- M.insert name <$> freshKindVar
  kindTable %= updateKindTable
  return $ TyVar name

instantiate ::
  ( HasFreshCount s
  , K.HasFreshCount s
  , HasKindTable s
  , MonadState s m
  , HasContext r
  , MonadReader r m
  )
  => TypeScheme
  -> m (Set Type, Type)
instantiate (Base ty) = pure (S.empty,ty)
instantiate (Forall vars cons ty) = do
  subs <- M.fromList <$> for (S.toList vars) makeFreshVar
  pure (S.map (substitute subs) cons, substitute subs ty)
  where
    makeFreshVar var = do
      var' <- fresh
      if TyVar var == var'
        then makeFreshVar var
        else pure (var, var')

occurs :: Identifier -> Type -> Bool
occurs name ty = name `S.member` freeInType ty

mgu
  :: ( AsTypeError e
     , AsKindError e
     , MonadError e m
     , K.HasFreshCount s
     , MonadState s m
     , HasKindTable r
     , MonadReader r m
     ) => Constraints -> m Substitution
mgu [] = pure M.empty
mgu (eq:eqs)
  | uncurry (==) eq = mgu eqs
  | otherwise = case eq of
      (TyVar name,ty)
        | occurs name ty -> throwError $ _OccursError # (name,ty)
        | otherwise -> do
            (kindSubs, kind) <- inferKind ty
            local (over kindTable $ subKindTable kindSubs) $ do
              kindInTable <- views kindTable $ M.lookup name
              updateKindTable <- case kindInTable of
                Just kind' -> do
                  kindSubs <- unifyKinds [(kind, kind')]
                  pure $ subKindTable kindSubs
                Nothing -> pure $ M.insert name kind
              let sub = M.singleton name ty
              subs <- local (over kindTable updateKindTable) (mgu $ substituteConstraint sub eqs)
              pure $ applySubs sub subs
      (ty,TyVar name) -> mgu $ (TyVar name,ty):eqs
      (TyApp con arg,TyApp con' arg') -> mgu $ (con,con'):(arg,arg'):eqs
      (ty,ty') -> throwError $ _TypeMismatch # (ty,ty')

findInstance :: (AsTypeError e, MonadError e m) => Type -> Type -> Map (Type,Type) Expr -> m ()
findInstance ty cons instances = unless ((ty,cons) `M.member` instances) . throwError $ _NoInstanceFound # (ty,cons)

kindPreservingSubstitution :: (AsKindError e, MonadError e m) => Substitution -> Map Identifier Kind -> m (Map Identifier Kind)
kindPreservingSubstitution subs = go (M.toList subs)
  where
    go [] ktable = pure ktable
    go ((name, value):rest) ktable =
      case M.lookup name ktable of
        Nothing -> throwError $ _KNotDefined # name
        Just k -> case value of
          TyVar name' -> case M.lookup name' ktable of
            Nothing -> throwError $ _KNotDefined # name'
            Just k' -> do
              kSubs <- unifyKinds [(k, k')]
              go rest . subKindTable kSubs $ M.delete name ktable
          _ -> go rest ktable

-- Checks that the second argument is more special that the first
special
  :: ( AsTypeError e
     , AsKindError e
     , MonadError e m
     , HasKindTable s
     , HasFreshCount s
     , K.HasFreshCount s
     , MonadState s m
     , HasContext r
     , MonadReader r m
     ) => TypeScheme -> TypeScheme -> m ()
special scheme scheme'
  | scheme == scheme' = pure ()
  | Forall vars cons ty <- scheme
  , Forall vars' cons' ty' <- scheme'
  = if vars == vars' && cons == cons'
      then use kindTable >>= void . runReaderT (unifyTypes ty ty')
      else do
        for_ (S.toList vars) $ \var -> do
          updateKindTable <- M.insertWith (flip const) var <$> freshKindVar
          kindTable %= updateKindTable
        for_ (S.toList vars') $ \var -> do
          updateKindTable <- M.insertWith (flip const) var <$> freshKindVar
          kindTable %= updateKindTable
        (cons, ty) <- instantiate scheme
        (cons', ty') <- instantiate scheme'
        -- The entailment relationship will have to come into play here I think
        subs <- use kindTable >>= runReaderT (unifyTypes ty ty')
        let newCons = S.map (substitute subs) cons
        newKindtable <- kindPreservingSubstitution subs =<< use kindTable
        kindTable .= newKindtable
        -- For each variable in each constraint, check that the target of the substitution has an instance
        for_ (S.toList newCons) $ \(TyApp predicate value) -> findInstance value predicate M.empty -- Should pass for every non-qualified type
  | Forall{} <- scheme , Base ty' <- scheme' = do
      (cons, ty) <- instantiate scheme
      subs <- use kindTable >>= runReaderT (unifyTypes ty ty')
      let newCons = S.map (substitute subs) cons
      for_ (S.toList newCons) $ \(TyApp predicate value) -> findInstance value predicate M.empty -- Should pass for every non-qualified type
  | Base ty <- scheme, Forall _ _ ty' <- scheme' =
      use kindTable >>= void . runReaderT (unifyTypes ty ty')
  | Base ty <- scheme, Base ty' <- scheme' = use kindTable >>= void . runReaderT (unifyTypes ty ty')
  where
    unifyTypes ty ty' = unifyTypes' ty ty' M.empty
      where
        unifyTypes' ty ty' ctxt
          | ty == ty' = pure ctxt
          | TyVar name <- ty
              = case M.lookup name ctxt of
                  Nothing -> pure $ M.insert name ty' ctxt
                  Just actualTy -> do
                    checkEquality actualTy ty'
                    pure ctxt
          | TyApp con arg <- ty, TyApp con' arg' <- ty' = do
              ctxt' <- unifyTypes' con con' ctxt
              unifyTypes' arg arg' ctxt'
          | otherwise = throwError $ _TypeMismatch # (ty,ty')

    checkEquality (TyApp con arg) (TyApp con' arg')
      = checkEquality con con' >> checkEquality arg arg'
    checkEquality ty ty' = unless (ty == ty') . throwError $ _TypeMismatch # (ty, ty')

runW :: Expr -> Either TypeError TypeScheme
runW = runExcept . flip evalStateT initialInferenceState . flip runReaderT initialInferenceState . w

runWithContext
  :: ( AsTypeError e
     , AsKindError e
     , MonadError e m
     ) => Map Identifier TypeScheme -> Expr -> m TypeScheme
runWithContext ctxt
  = flip evalStateT initialInferenceState .
    flip runReaderT initialInferenceState { _context = ctxt } . w

type MonadW r s e m
  = ( HasFreshCount s
    , K.HasFreshCount s
    , HasKindTable s
    , MonadState s m
    , HasContext r
    , MonadReader r m
    , AsTypeError e
    , AsKindError e
    , MonadError e m
    )

patType ::
  ( HasFreshCount s
  , K.HasFreshCount s
  , HasKindTable s
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
  (_,conTy) <- instantiate =<< lookupId conName
  let (retTy,argTys) = conArgTypes conTy
      argsLen = length args
      argTysLen = length argTys
  when (argsLen /= argTysLen) . throwError $ _PatternArgMismatch # (argsLen,argTysLen)
  let boundVars = foldr (\(arg,argTy) -> M.insert arg (Base argTy)) M.empty $ zip args argTys
  return (boundVars,retTy)
patType (PatLit (LitInt p)) = return (M.empty,TyPrim Int)
patType (PatLit (LitString p)) = return (M.empty,TyPrim String)
patType (PatLit (LitChar p)) = return (M.empty,TyPrim Char)
patType (PatLit (LitBool p)) = return (M.empty,TyPrim Bool)
patType PatWildcard = (,) M.empty <$> fresh

entails :: Set Type -> Set Type -> Bool
entails = undefined

w :: MonadW r s e m => Expr -> m TypeScheme
w e = do
  (subs,cons,ty) <- w' e
  ctxt <- view context
  return $ generalize ctxt (S.map (substitute subs) cons, substitute subs ty)
  where
    inferBranches :: MonadW r s e m => NonEmpty (Pattern,Expr) -> m (Substitution, [(Type,Set Type,Type)])
    inferBranches = foldrM inferBranch (M.empty,[])
      where
        inferBranch (pat,branch) (subs,bTypes) = do
          (boundVars,patternType) <- patType pat
          local (over context $ M.union boundVars) $ do
            (branchSubs,preds,branchType) <- w' branch
            pure (applySubs branchSubs subs, (patternType,preds,branchType):bTypes)

    w' :: MonadW r s e m => Expr -> m (Substitution, Set Type, Type)
    w' e = case e of
        (Error _) -> (,,) M.empty S.empty <$> fresh
        (Id name) -> do
          (cons,ty) <- lookupId name >>= instantiate
          pure (M.empty,cons,ty)
        (Lit (LitInt e)) -> return (M.empty,S.empty,TyPrim Int)
        (Lit (LitString e)) -> return (M.empty,S.empty,TyPrim String)
        (Lit (LitChar e)) -> return (M.empty,S.empty,TyPrim Char)
        (Lit (LitBool e)) -> return (M.empty,S.empty,TyPrim Bool)
        (App f x) -> do
          (s1,cons1,t1) <- w' f
          (s2,cons2,t2) <- local (over context $ subContext s1) $ w' x
          b <- fresh
          s3 <- use kindTable >>= runReaderT (mgu [(TyFun t2 b,substitute s2 t1)])
          let cons3 = S.map (substitute $ applySubs s3 s2) cons1 `S.union` S.map (substitute s3) cons2
          return (applySubs s3 $ applySubs s2 s1, cons3, substitute s3 b)
        (Abs x expr) -> do
          ctxt <- get
          b <- fresh
          (s1,cons,t1) <- local (over context $ M.insert x (Base b)) $ w' expr
          return (s1,cons,TyFun (substitute s1 b) t1)
        (Let (Binding x e) e') -> do
          (s1,cons1,t1) <- w' e
          let addVar ctxt = let ctxt' = subContext s1 ctxt in M.insert x (generalize ctxt' (cons1,t1)) ctxt'
          (s2,cons2,t2) <- local (over context addVar) $ w' e'
          return (applySubs s2 s1, S.union cons2 $ S.map (substitute s2) cons1, t2)
        (Rec (Binding name value) rest) -> do
          freshVar <- fresh
          (s1,cons1,t1) <- local (over context . M.insert name $ Base freshVar) $ w' value
          s2 <- use kindTable >>= runReaderT (mgu $ (t1,freshVar) : M.toList (M.mapKeys TyVar s1))
          let cons1' = S.map (substitute s2) cons1
          (s3,cons2,t2) <- local (over context $ \ctxt -> M.insert name (generalize ctxt (cons1', substitute s2 t1)) $ subContext s1 ctxt) $ w' rest
          pure (applySubs s3 s1,S.map (substitute s3) $ cons1' `S.union` cons2, t2)
        (Case input bs) -> do
          (s1,cons,inputType) <- w' input
          (bSubs,bs') <- inferBranches bs
          outputType <- fresh
          let equations = foldr (\(p,_,b) eqs -> (p,inputType):(b,outputType):eqs) [] bs'
          subs <- use kindTable >>= runReaderT (mgu equations)
          let constraints = foldr (\(_,c,_) constrs -> S.map (substitute subs) c `S.union` constrs) S.empty bs'
          pure (applySubs subs $ applySubs bSubs s1,constraints,substitute subs outputType)

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
  , K.HasFreshCount s
  , MonadState s m
  , AsTypeError e
  , AsKindError e
  , MonadError e m
  )
  => Definition
  -> m (Map Identifier Expr)
checkDefinition (Data tyCon tyVars decls) = do
  freshCount .= 0
  kind <- get >>= checkDefinitionKinds tyCon tyVars decls
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
          context %= M.insert dataCon (generalize ctxt (S.empty,conFun))
          return (dataCon, buildDataCon p)

checkDefinition (Function (Binding name expr)) = do
  freshCount .= 0
  maybeVar <- uses context (M.lookup name)
  case maybeVar of
    Nothing -> do
      ctxt <- use context
      ty <- get >>= runReaderT (w expr)
      maybeSig <- use (typesignatures . at name)
      case maybeSig of
        Nothing -> pure ()
        Just expected -> do
          K.freshCount .= 0
          get >>= runReaderT (special ty expected)
      context %= M.insert name ty
      return $ M.singleton name expr
    _ -> throwError $ _AlreadyDefined # name

checkDefinition (TypeSignature name ty) = do
  maybeSig <- use (typesignatures . at name)
  case maybeSig of
    Nothing -> do
      case ty of
        Forall vars cons ty -> do
          table <- use kindTable
          subs <- validateConstraintKinds table $ S.toList cons
          void . flip runStateT (KindInferenceState 0) $ do
            let vars' = S.toList $ S.map (\a -> (a,substituteKind subs $ KindVar a)) vars
            flip runReaderT (M.fromList vars' `M.union` table) $ inferKind ty
        Base ty -> do
          table <- use kindTable
          void . flip runStateT (KindInferenceState 0) $ runReaderT (inferKind ty) table
      typesignatures %= M.insert name ty
    _ -> throwError $ _DuplicateTypeSignatures # name
  pure M.empty
  where
    validateConstraintKinds table [] = pure M.empty
    validateConstraintKinds table (con:cons) = do
      (subs,k) <- runInferKind con table
      unifyKinds [(k,Constraint)]
      subs' <- validateConstraintKinds (applyKindSubs subs table) cons
      pure (applyKindSubs subs' subs)

checkDefinitions ::
  ( HasFreshCount s
  , HasKindTable s
  , HasContext s
  , HasTypesignatures s
  , K.HasFreshCount s
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
