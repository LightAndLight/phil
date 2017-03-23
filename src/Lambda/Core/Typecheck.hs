{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts       #-}

module Lambda.Core.Typecheck where

import Debug.Trace

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

import           Lambda.Core.AST.Binding
import           Lambda.Core.AST.Definitions
import           Lambda.Core.AST.Expr
import           Lambda.Core.AST.Evidence
import           Lambda.Core.AST.Identifier
import           Lambda.Core.AST.Lens
import           Lambda.Core.AST.Literal
import           Lambda.Core.AST.Types
import           Lambda.Core.AST.Pattern
import qualified Lambda.Core.Kinds as K (HasFreshCount(..))
import Lambda.Core.Kinds hiding (HasFreshCount(..))
import Lambda.Core.Typeclasses
import Lambda.Core.Typecheck.Unification

data InferenceState
  = InferenceState
    { _isContext    :: Map Identifier TypeScheme
    , _isTypesignatures :: Map Identifier TypeScheme
    , _isKindTable  :: Map Identifier Kind
    , _isKindInferenceState :: KindInferenceState
    , _isFreshCount :: Int
    , _isTcContext :: [TypeclassEntry]
    , _isEVarCount :: Int
    }

makeClassy ''InferenceState

initialInferenceState
  = InferenceState
  { _isContext = M.empty
  , _isTypesignatures = M.empty
  , _isKindTable = M.empty
  , _isKindInferenceState = initialKindInferenceState
  , _isFreshCount = 0
  , _isTcContext = []
  , _isEVarCount = 0
  }

class HasContext s where
  context :: Lens' s (Map Identifier TypeScheme)

class HasTypesignatures s where
  typesignatures :: Lens' s (Map Identifier TypeScheme)

class HasFreshCount s where
  freshCount :: Lens' s Int

instance HasContext InferenceState where
  context = inferenceState . isContext

instance HasTypesignatures InferenceState where
  typesignatures = inferenceState . isTypesignatures

instance HasKindTable InferenceState where
  kindTable = inferenceState . isKindTable

instance HasFreshCount InferenceState where
  freshCount = inferenceState . isFreshCount

instance HasKindInferenceState InferenceState where
  kindInferenceState = inferenceState . isKindInferenceState

instance K.HasFreshCount InferenceState where
  freshCount = inferenceState . isKindInferenceState . K.freshCount

instance HasTcContext InferenceState where
  tcContext = inferenceState . isTcContext

instance HasEVarCount InferenceState where
  eVarCount = inferenceState . isEVarCount

data TypeError
  = NotInScope [String]
  | PatternArgMismatch Int Int
  | AlreadyDefined Identifier
  | TooManyArguments TypeScheme
  | WrongArity [Type]
  | NotDefined Identifier
  | DuplicateTypeSignatures Identifier
  | KindInferenceError KindError
  | CouldNotDeduce [Type] [Type]
  | NoSuchClass Identifier
  | NonClassFunction Identifier [Type] Identifier
  | MissingClassFunctions Identifier [Type] (Set Identifier)
  | TUnificationError (UnificationError Type)
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

free :: Map Identifier TypeScheme -> Set Identifier
free = foldr (\scheme frees -> freeInScheme scheme `S.union` frees) S.empty

generalize
  :: ( HasContext r
     , MonadReader r m
     , HasTcContext env
     , HasEVarCount s
     , MonadState s m
     ) => env -> Expr -> [(EVar, Type)] -> Type -> m (Expr, TypeScheme)
generalize env expr cons ty = do
  ctxt <- view context
  let frees = freeInType ty
  let (cons', solved) = partition (\(_, ty) -> freeInType ty /= S.empty) cons
  let expr' = foldr (uncurry replaceDictionaries) expr $ fmap (second Dict) (traceShow "solved" $ traceShowId solved)
  -- let expr'' = foldr DictAbs expr' $ fst <$> (traceShow "cons" $ traceShowId cons')
  let expr'' = foldr DictAbs expr $ fst <$> (traceShow "cons" $ traceShowId cons')
  pure
    ( expr''
    , Forall ((frees `S.union` foldr (\el set -> freeInType el `S.union` set) S.empty (snd <$> cons')) `S.difference` free ctxt) (snd <$> cons') ty
    )

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
  -> m ([Type], Type)
instantiate (Forall vars cons ty) = do
  subs <- Substitution <$> for (S.toList vars) makeFreshVar
  pure (fmap (substitute subs) cons, substitute subs ty)
  where
    makeFreshVar var = do
      var' <- fresh
      if TyVar var == var'
        then makeFreshVar var
        else pure (var, var')

kindPreservingSubstitution
  :: ( AsKindError e
     , MonadError e m
     , HasKindTable r
     , MonadReader r m
     ) => Substitution Type -> m ()
kindPreservingSubstitution subs = go $ getSubstitution subs
  where
    go [] = pure ()
    go ((name, targetType):rest) = do
      table <- view kindTable
      kind <- lookupKind name table
      case targetType of
        TyVar name' -> do
          kind' <- lookupKind name' table
          either (throwError . review _KUnificationError) (const $ go rest) $ unify [(kind, kind')]
        _ -> go rest

-- Checks that the second argument is more special that the first
special
  :: ( AsTypeError e
     , AsKindError e
     , MonadError e m
     , HasKindTable s
     , HasFreshCount s
     , K.HasFreshCount s
     , MonadState s m
     , HasTcContext r
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
        (cons, ty) <- instantiate scheme -- this would be the body's type
        (cons', ty') <- instantiate scheme' -- this would be the signature
        subs <- Substitution . M.toList <$> (use kindTable >>= runReaderT (unifyTypes ty ty'))
        use kindTable >>= runReaderT (kindPreservingSubstitution subs)
        tctxt <- view tcContext
        let newCons' = fmap (substitute subs) cons' -- more special
            newCons = fmap (substitute subs) cons -- more general
            generalCons = cons ++ newCons'
            specialCons = cons' ++ newCons
        dicts <- flip evalStateT (0 :: Int) $ do
          generalCons' <- for generalCons $ \g -> (,) <$> freshEVar <*> pure g
          specialCons' <- for specialCons $ \s -> (,) <$> freshEVar <*> pure s
          traverse (entails tctxt generalCons') specialCons'
        case sequence dicts of
          Just{} -> pure ()
          Nothing -> throwError $ _CouldNotDeduce # (specialCons, newCons')
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
          | otherwise = throwError $ _TUnificationError # CannotUnify ty ty'

    checkEquality (TyApp con arg) (TyApp con' arg')
      = checkEquality con con' >> checkEquality arg arg'
    checkEquality ty ty' = unless (ty == ty') . throwError $ _TUnificationError # CannotUnify ty ty'

runW :: Expr -> Either TypeError (Expr, TypeScheme)
runW = runExcept . flip evalStateT initialInferenceState . flip runReaderT initialInferenceState . w

runWithContext
  :: ( AsTypeError e
     , AsKindError e
     , MonadError e m
     ) => Map Identifier TypeScheme -> Expr -> m (Expr, TypeScheme)
runWithContext ctxt
  = flip evalStateT initialInferenceState .
    flip runReaderT initialInferenceState { _isContext = ctxt } . w

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
  return (M.singleton name $ Forall S.empty [] ty,ty)
patType (PatCon conName args) = do
  (_,conTy) <- instantiate =<< lookupId conName
  let (retTy,argTys) = conArgTypes conTy
      argsLen = length args
      argTysLen = length argTys
  when (argsLen /= argTysLen) . throwError $ _PatternArgMismatch # (argsLen,argTysLen)
  let boundVars = foldr (\(arg,argTy) -> M.insert arg (Forall S.empty [] argTy)) M.empty $ zip args argTys
  return (boundVars,retTy)
patType (PatLit (LitInt p)) = return (M.empty,TyPrim Int)
patType (PatLit (LitString p)) = return (M.empty,TyPrim String)
patType (PatLit (LitChar p)) = return (M.empty,TyPrim Char)
patType (PatLit (LitBool p)) = return (M.empty,TyPrim Bool)
patType PatWildcard = (,) M.empty <$> fresh

replaceDictionaries :: EVar -> Dictionary -> Expr -> Expr
replaceDictionaries eVar dict expr = case expr of
    Prod cons exprs -> Prod cons $ fmap (replaceDictionaries eVar dict) exprs
    App f x -> App (replaceDictionaries eVar dict f) (replaceDictionaries eVar dict x)
    Abs name body -> Abs name (replaceDictionaries eVar dict body)
    DictAbs eVar' body
      | eVar /= eVar' -> DictAbs eVar' (replaceDictionaries eVar dict body)
      | otherwise -> expr
    DictApp expr' evidence -> DictApp (replaceDictionaries eVar dict expr') $ subDict (eVar, dict) evidence
    DictSel name evidence -> DictSel name $ subDict (eVar, dict) evidence
    Let (Binding name value) rest -> Let (Binding name $ replaceDictionaries eVar dict value) (replaceDictionaries eVar dict rest)
    Rec (Binding name value) rest -> Rec (Binding name $ replaceDictionaries eVar dict value) (replaceDictionaries eVar dict rest)
    Case input branches -> Case (replaceDictionaries eVar dict input) $ fmap (second $ replaceDictionaries eVar dict) branches
    _ -> expr

w :: (MonadW r s e m, HasEVarCount s, HasTcContext s) => Expr -> m (Expr, TypeScheme)
w e = do
  (subs, cons, ty, e') <- w' e
  env <- get
  (e'', ty') <- generalize env e' cons $ substitute subs ty
  return (e'', ty')
  where
    inferBranches :: (MonadW r s e m, HasEVarCount s, HasTcContext s) => NonEmpty (Pattern,Expr) -> m (Substitution Type, [(Type, [(EVar, Type)], Type, Expr)])
    inferBranches = foldrM inferBranch (mempty,[])
      where
        inferBranch (pat,branch) (subs,bTypes) = do
          (boundVars,patternType) <- patType pat
          local (over context $ M.union boundVars) $ do
            (branchSubs,preds,branchType,branch') <- w' branch
            pure (branchSubs <> subs, (patternType, preds, branchType, branch'):bTypes)

    w' :: (MonadW r s e m, HasEVarCount s, HasTcContext s) => Expr -> m (Substitution Type, [(EVar, Type)], Type, Expr)
    w' e = case e of
        (Error _) -> (,,,) mempty [] <$> fresh <*> pure e
        (Id name) -> do
          (cons, ty) <- lookupId name >>= instantiate
          tctxt <- use tcContext
          cons' <- for cons $ \c -> (,) <$> freshEVar <*> pure c
          Just dicts <- sequence <$> traverse (buildDictionary tctxt cons') cons'
          pure (mempty, cons', ty, foldl' DictApp e (snd <$> dicts))
        (Lit (LitInt _)) -> return (mempty, [], TyPrim Int, e)
        (Lit (LitString _)) -> return (mempty, [], TyPrim String, e)
        (Lit (LitChar _)) -> return (mempty, [], TyPrim Char, e)
        (Lit (LitBool _)) -> return (mempty, [], TyPrim Bool, e)
        (App f x) -> do
          (s1, cons1, t1, f') <- w' f
          (s2, cons2, t2, x') <- local (over context $ fmap (subTypeScheme s1)) $ w' x
          b <- fresh
          s3 <- either (throwError . review _TUnificationError) pure $ unify [(TyFun t2 b,substitute s2 t1)]
          return
            ( s3 <> s2 <> s1
            , fmap (second $ substitute s3) (fmap (second $ substitute s2) cons1 ++ cons2)
            , substitute s3 b
            , App f' x'
            )
        (Abs x expr) -> do
          b <- fresh
          (s1, cons, t1, expr') <- local (over context $ M.insert x (Forall S.empty [] b)) $ w' expr
          return (s1, cons, TyFun (substitute s1 b) t1, Abs x expr')
        (Let (Binding x e) e') -> do
          (s1, cons1, t1, e1) <- w' e
          (s2, cons2, t2, e2) <- local (over context $ fmap (subTypeScheme s1)) $ do
            env <- get
            (e1', t1') <- generalize env e1 cons1 t1
            local (over context $ M.insert x t1') $ w' e'
          return (s2 <> s1, cons2, t2, Let (Binding x $ foldr DictAbs e1 (fst <$> cons1)) e2)
        (Rec (Binding name value) rest) -> do
          freshVar <- fresh
          (s1, cons1, t1, value') <- local (over context . M.insert name $ Forall S.empty [] freshVar) $ w' value
          s2 <- either (throwError . review _TUnificationError) pure . unify $ (t1,freshVar) : (first TyVar <$> getSubstitution s1)
          let cons1' = fmap (second $ substitute s2) cons1
          (s3, cons2, t2, rest', cons1'', value'') <- local (over context $ fmap (subTypeScheme s1)) $ do
            env <- get
            (_, t1') <- generalize env value' cons1' (substitute s2 t1)
            local (over context $ M.insert name t1') $ do
              (sub, cons, ty, rest') <- w' rest
              (_, cons1'', _, value'') <- w' value
              pure (sub, cons, ty, rest', cons1'', value'')
          pure (s3 <> s1, cons2, t2, Rec (Binding name $ foldr DictAbs value'' (fst <$> cons1'')) rest')
        (Case input bs) -> do
          (s1, cons, inputType, input') <- w' input
          (bSubs,bs') <- inferBranches bs
          outputType <- fresh
          let equations = foldr (\(p,_,b,_) eqs -> (p,inputType):(b,outputType):eqs) [] bs'
          subs <- either (throwError . review _TUnificationError) pure $ unify equations
          let cons' = fmap (second $ substitute subs) $ cons ++ join (fmap (\(_, c, _, _) -> c) bs')
          let bs'' = N.zip (fst <$> bs) ((\(_, _, _, b) -> b) <$> N.fromList bs')
          pure
            ( subs <> bSubs <> s1
            , cons'
            , substitute subs outputType
            , Case input' bs''
            )

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
  , HasTcContext s
  , HasEVarCount s
  , MonadState s m
  , AsTypeError e
  , AsKindError e
  , MonadError e m
  )
  => Definition
  -> m (Map Identifier Expr, Definition)

checkDefinition def@(Class supers constructor params funcs) = do
  freshVar <- freshKindVar
  paramKinds <- for params (\param -> (,) param <$> freshKindVar)
  kindTable %= M.insert constructor (foldr KindArrow Constraint $ snd <$> paramKinds)
  table <- use kindTable
  let constructorTy = foldl' TyApp (TyCon $ TypeCon constructor) $ TyVar <$> params
  (subs, classKind) <- flip runReaderT (M.fromList paramKinds `M.union` table) $ do
    subs <- checkConstraints supers
    local (subKindTable subs) $ do
      let freeVars = foldMap freeInType (S.fromList $ fmap snd funcs) `S.difference` foldMap freeInType (S.fromList $ constructorTy : supers)
      varsWithKinds <- fmap M.fromList . for (S.toList freeVars) $ \var -> (,) var <$> freshKindVar
      local (M.union varsWithKinds) $ do
        subs' <- checkSignatures $ fmap snd funcs
        (subs'', kind) <- local (fmap $ substitute subs') $ inferKind (TyCon (TypeCon constructor))
        pure (subs'' <> subs' <> subs, kind)
  kindTable %= subKindTable subs
  checkedFuncs <- for funcs $ \(name, ty) -> do
    eVar <- freshEVar
    env <- get
    (expr, checkedFuncTy) <- get >>= runReaderT (generalize env (DictAbs eVar $ DictSel name (Variable eVar)) [(eVar, constructorTy)] ty)
    context %= M.insert name checkedFuncTy
    pure (name, checkedFuncTy, expr)
  tcContext %= (TceClass supers constructorTy (M.fromList $ fmap (\(name, ty, _) -> (name, ty)) checkedFuncs) :)
  eVar <- freshEVar
  pure (M.fromList $ fmap (\(name, _, expr) -> (name, expr)) checkedFuncs, def)
  where
    checkSignatures [] = pure mempty
    checkSignatures (sig:rest) = do
      (subs, _) <- inferKind sig
      subs' <- checkSignatures rest
      pure $ subs' <> subs

checkDefinition (Instance supers constructor params impls) = do
  entry <- uses tcContext $ getClass constructor
  let constructorTy = foldl' TyApp (TyCon $ TypeCon constructor) params
  get >>= runReaderT (inferKind constructorTy)
  impls' <- case entry of
    Nothing -> throwError $ _NoSuchClass # constructor
    Just (TceClass supers ty members)
      | let implNames = S.fromList (fmap bindingName impls)
      , let memberNames = M.keysSet members
      , let notImplemented = memberNames `S.difference` implNames
      , notImplemented /= S.empty -> throwError $ _MissingClassFunctions # (constructor, params, notImplemented)
      | otherwise -> for impls $ \(Binding implName impl) ->
          case M.lookup implName members of
            Nothing -> throwError $ _NonClassFunction # (constructor, params, implName)
            Just implTy -> do
              let inst = TceInst supers constructorTy undefined
              st <- get
              flip runReaderT st . local (over tcContext (inst :)) $ do
                (impl', ty) <- w impl
                special implTy ty
                pure $ Binding implName impl'
  let inst = TceInst supers constructorTy . M.fromList $ fmap (\(Binding name expr) -> (name, expr)) impls'
  tcContext %= (inst :)
  pure (M.empty, Instance supers constructor params impls')

checkDefinition def@(Data tyCon tyVars decls) = do
  freshCount .= 0
  table <- use kindTable
  kind <- runReaderT (checkDefinitionKinds tyCon tyVars decls) table
  kindTable %= M.insert tyCon kind
  let tyVars' = fmap TyVar tyVars
  liftA2 (,) (M.fromList <$> traverse (checkDataDecl tyCon tyVars') (N.toList decls)) $ pure def
  where
    checkDataDecl tyCon tyVars p@(ProdDecl dataCon argTys) = do
      maybeCon <- use (context . at dataCon)
      case maybeCon of
        Just _ -> throwError $ _AlreadyDefined # dataCon
        Nothing -> do
          let conTy = flip (foldr TyFun) argTys $ foldl' TyApp (TyCon $ TypeCon tyCon) tyVars
          ctxt <- use context
          let conExpr = buildDataCon p
          env <- get
          (conExpr', conTy') <- get >>= runReaderT (generalize env conExpr [] conTy)
          context %= M.insert dataCon conTy'
          return (dataCon, conExpr')

checkDefinition (Function (Binding name expr)) = do
  freshCount .= 0
  maybeVar <- uses context (M.lookup name)
  case maybeVar of
    Nothing -> do
      ctxt <- use context
      (expr', ty) <- get >>= runReaderT (w expr)
      maybeSig <- use (typesignatures . at name)
      case maybeSig of
        Nothing -> context %= M.insert name ty
        Just expected -> do
          K.freshCount .= 0
          get >>= runReaderT (special ty expected)
          context %= M.insert name expected
      return (M.singleton name expr', Function $ Binding name expr')
    _ -> throwError $ _AlreadyDefined # name

checkDefinition def@(TypeSignature name scheme@(Forall vars cons ty)) = do
  maybeSig <- use (typesignatures . at name)
  case maybeSig of
    Nothing -> do
      table <- use kindTable
      void $ do
        kindVars <- for (S.toList vars) $ \var -> (,) var <$> freshKindVar
        flip runReaderT (M.fromList kindVars `M.union` table) $ do
          subs <- checkConstraints cons
          t <- view kindTable
          res <- local (subKindTable subs) $ inferKind ty
          pure res
      typesignatures %= M.insert name scheme
    _ -> throwError $ _DuplicateTypeSignatures # name
  pure (M.empty, def)

checkDefinitions ::
  ( HasFreshCount s
  , HasKindTable s
  , HasContext s
  , HasTypesignatures s
  , K.HasFreshCount s
  , HasTcContext s
  , HasEVarCount s
  , MonadState s m
  , AsTypeError e
  , AsKindError e
  , MonadError e m
  )
  => [Definition]
  -> m [Definition]
checkDefinitions defs = fmap snd <$> traverse checkDefinition defs
