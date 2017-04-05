{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE MultiParamTypeClasses       #-}

module Lambda.Typecheck where

import           Control.Applicative
import Control.Arrow ((***))
import           Control.Lens
import           Control.Monad.Except
import           Control.Monad.Fresh
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

import           Lambda.AST (everywhere, toCoreExpr)
import           Lambda.AST.Binding
import           Lambda.AST.Definitions
import           Lambda.AST.Expr
import           qualified Lambda.Core.AST.Expr as C
import           Lambda.Core.AST.Identifier
import           Lambda.Core.AST.InstanceHead
import           Lambda.Core.AST.Lens
import           Lambda.Core.AST.Literal
import           Lambda.Core.AST.Types
import           Lambda.Core.AST.Pattern
import           Lambda.Core.AST.ProdDecl
import Lambda.Core.Kinds
import Lambda.Sugar (asClassInstanceP, desugarExpr)
import Lambda.Typecheck.Entailment
import Lambda.Typecheck.TypeError
import Lambda.Typecheck.Unification
import Lambda.Typeclasses

data ContextEntry
  -- | Overloaded function entry
  = OEntry { typeScheme :: TypeScheme }
  -- | Constructor entry
  | CEntry { typeScheme :: TypeScheme } 
  -- | Function entry
  | FEntry { typeScheme :: TypeScheme } 
  -- | Recursive entry
  | REntry { typeScheme :: TypeScheme } 

subContextEntry subs entry
  = entry { typeScheme = subTypeScheme subs (typeScheme entry) }

data InferenceState
  = InferenceState
    { _isContext    :: Map Identifier ContextEntry
    , _isTypesignatures :: Map Identifier TypeScheme
    , _isKindTable  :: Map Identifier Kind
    , _isTcContext :: [TypeclassEntry C.Expr]
    }

makeClassy ''InferenceState

initialInferenceState
  = InferenceState
  { _isContext = M.empty
  , _isTypesignatures = M.empty
  , _isKindTable = M.fromList 
      [ ("Int", Star)
      , ("Bool", Star)
      , ("String", Star)
      , ("Char", Star)
      ]
  , _isTcContext = []
  }

class HasContext s where
  context :: Lens' s (Map Identifier ContextEntry)

class HasTypesignatures s where
  typesignatures :: Lens' s (Map Identifier TypeScheme)

instance HasContext InferenceState where
  context = inferenceState . isContext

instance HasTypesignatures InferenceState where
  typesignatures = inferenceState . isTypesignatures

instance HasKindTable InferenceState where
  kindTable = inferenceState . isKindTable

instance HasTcContext C.Expr InferenceState where
  tcContext = inferenceState . isTcContext

lookupId ::
  ( HasContext r
  , MonadReader r m
  , AsTypeError e
  , MonadError e m
  )
  => Identifier
  -> m ContextEntry
lookupId name = do
  maybeTy <- view (context . at name)
  case maybeTy of
    Just ty -> return ty
    Nothing -> throwError $ _NotInScope # [name]

conArgTypes :: Type -> (Type,[Type])
conArgTypes (TyFun from to) = (from :) <$> conArgTypes to
conArgTypes ty = (ty,[])

free :: Map Identifier TypeScheme -> Set Identifier
free = foldMap freeInScheme

-- | Generalize a type scheme
-- |
-- | During generalization, the following takes place:
-- |
-- | - 
generalize
  :: ( MonadFresh m
     , HasContext r
     , MonadReader r m
     , AsTypeError e
     , MonadError e m
     )
  => Substitution Type -- ^ Substitutions to apply to placeholders
  -> [TypeclassEntry a] -- ^ Typeclass environment
  -> Expr -- ^ Expression to operate on
  -> [Type] -- ^ Constraints
  -> [Placeholder] -- ^ Dictionary parameter environment
  -> Type -- ^ Type to generalize
  -> m (Expr, TypeScheme)
generalize subs tcenv expr cons dictParams ty = do
  ctxt <- view context
  let freeInCtxt = free $ typeScheme <$> ctxt
  let frees = (freeInType ty `S.union` foldMap freeInType cons)
        `S.difference` freeInCtxt
  let (newCons, placeholderMapping) = simplify tcenv cons

  let dictParams' = fmap N.fromList . fromJust . ctorAndArgs <$> newCons
  (dictParams'', mapping) <- resolvePlaceholders tcenv dictParams' freeInCtxt

  let expr' = updatePlaceholders placeholderMapping $ everywhere subPlaceholders expr
  let expr'' = everywhere (replacePlaceholders $ M.fromList mapping) expr'

  let unresolved = foldr fromDictVar [] $ snd <$> mapping

  let newCons' = filter ((S.empty /=) . freeInType) newCons
  pure (foldr Abs expr'' unresolved, Forall frees newCons' ty)
  where
    subPlaceholders (DictPlaceholder (className, tyArgs))
      = DictPlaceholder (className, substitute subs <$> tyArgs)
    subPlaceholders expr = expr

    fromDictVar (DictVar a) as = a : as
    fromDictVar _ as = as

freshTyVar :: (MonadFresh m, HasKindTable s, MonadState s m) => m Type
freshTyVar = do
  name <- ("t" ++) <$> fresh
  updateKindTable <- M.insert name <$> freshKindVar
  kindTable %= updateKindTable
  return $ TyVar name

instantiate ::
  ( MonadFresh m
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
      var' <- freshTyVar
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
  :: ( MonadFresh m
     , AsTypeError e
     , AsKindError e
     , MonadError e m
     , HasKindTable s
     , MonadState s m
     , HasTcContext C.Expr r
     , HasContext r
     , MonadReader r m
     ) => TypeScheme -> TypeScheme -> m ()
special scheme scheme'
  | scheme == scheme' = pure ()
  | Forall vars cons ty <- scheme
  , Forall vars' cons' ty' <- scheme'
  , vars' `S.intersection` freeInScheme scheme == S.empty
  = do
    subs <- Substitution . M.toList <$> unifyTypes vars ty ty'
    tctxt <- view tcContext
    let consSubbed = substitute subs <$> cons
    unless (all (entails tctxt cons') consSubbed) .
      throwError $ _CouldNotDeduce # (consSubbed, cons')
  | otherwise = throwError $ _TypeMismatch # (scheme, scheme')
  where
    unifyTypes bound ty ty' = unifyTypes' ty ty' M.empty
      where
        unifyTypes' ty ty' ctxt
          | ty == ty' = pure ctxt
          | TyVar name <- ty
          , name `S.member` bound
          = case M.lookup name ctxt of
              Nothing -> pure $ M.insert name ty' ctxt
              Just actualTy
                | actualTy /= ty' -> throwError $ _TUnificationError # CannotUnify actualTy ty'
                | otherwise -> pure ctxt
          | TyApp con arg <- ty, TyApp con' arg' <- ty' = do
              ctxt' <- unifyTypes' arg arg' ctxt
              unifyTypes' con con' ctxt'
          | otherwise = throwError $ _TUnificationError # CannotUnify ty ty'

runInferType :: Expr -> Either TypeError (Expr, TypeScheme)
runInferType = runExcept . runFreshT . flip evalStateT initialInferenceState . flip runReaderT initialInferenceState . inferType

type MonadW r s e m
  = ( MonadFresh m
    , HasKindTable s
    , HasTcContext C.Expr s
    , MonadState s m
    , HasContext r
    , MonadReader r m
    , AsTypeError e
    , AsKindError e
    , MonadError e m
    )

patType ::
  ( MonadFresh m
  , HasKindTable s
  , MonadState s m
  , HasContext r
  , MonadReader r m
  , AsTypeError e
  , MonadError e m
  )
  => Pattern
  -> m (Map Identifier ContextEntry,Type)
patType (PatId name) = do
  ty <- freshTyVar
  return (M.singleton name . FEntry $ Forall S.empty [] ty,ty)
patType (PatCon conName args) = do
  (_,conTy) <- instantiate . typeScheme =<< lookupId conName
  let (retTy,argTys) = conArgTypes conTy
      argsLen = length args
      argTysLen = length argTys
  when (argsLen /= argTysLen) . throwError $ _PatternArgMismatch # (argsLen,argTysLen)
  let boundVars = foldr (\(arg,argTy) -> M.insert arg (FEntry $ Forall S.empty [] argTy)) M.empty $ zip args argTys
  return (boundVars,retTy)
patType (PatLit (LitInt p)) = return (M.empty, TyCtor "Int")
patType (PatLit (LitString p)) = return (M.empty, TyCtor "String")
patType (PatLit (LitChar p)) = return (M.empty, TyCtor "Char")
patType (PatLit (LitBool p)) = return (M.empty, TyCtor "Bool")
patType PatWildcard = (,) M.empty <$> freshTyVar

runWithContext
  :: ( AsTypeError e
     , AsKindError e
     , MonadError e m
     ) => Map Identifier ContextEntry -> Expr -> m (Expr, TypeScheme)
runWithContext ctxt
  = runFreshT .
    flip evalStateT initialInferenceState .
    flip runReaderT initialInferenceState { _isContext = ctxt } . inferType

inferType :: (MonadW r s e m, HasTcContext C.Expr s) => Expr -> m (Expr, TypeScheme)
inferType e = do
  (subs, cons, dictParams, ty, e') <- w e
  env <- use tcContext
  generalize subs env e' (substitute subs <$> cons) dictParams (substitute subs ty)
  where
    w :: MonadW r s e m => Expr -> m (Substitution Type, [Type], [Placeholder], Type, Expr)
    w e = case e of
      Error _ -> (,,,,) mempty [] [] <$> freshTyVar <*> pure e
      Id name -> inferIdent name
      Lit lit -> inferLiteral lit
      App f x -> inferApp f x
      Abs x expr -> inferAbs x expr
      Let binding rest -> inferLet binding rest
      Rec binding rest -> inferRec binding rest
      Case input bs -> inferCase input bs
      _ -> error $ "inferType: invalid expression: " ++ show e

    inferIdent :: MonadW r e s m => Identifier -> m (Substitution Type, [Type], [Placeholder], Type, Expr)
    inferIdent name = do
      entry <- lookupId name
      case entry of
        OEntry scheme -> do
          ([cons], ty) <- instantiate scheme
          ([placeholder], env) <- consToPlaceholders [cons]
          pure
            ( mempty
            , [cons]
            , env
            , ty
            , DictSel name placeholder
            )
        REntry scheme -> do
          (cons, ty) <- instantiate scheme
          (placeholders, env) <- consToPlaceholders cons
          pure
            ( mempty
            , cons
            , env
            , ty
            , RecPlaceholder name
            )
        _ -> do
          (cons, ty) <- instantiate $ typeScheme entry
          (placeholders, env) <- consToPlaceholders cons
          pure
            ( mempty
            , cons
            , env
            , ty
            , foldl' App (Id name) placeholders
            )

      where
        consToPlaceholders [] = pure ([], [])
        consToPlaceholders (cons : rest)
          = let Just (className, instArgs) = ctorAndArgs cons
            in do
              dvar <- ("dict" ++) <$> fresh
              bimap
                (DictPlaceholder (className, N.fromList instArgs) :)
                ((className, N.fromList instArgs) :)
                <$> consToPlaceholders rest

    inferLiteral lit = case lit of
      LitInt _ -> return (mempty, [], [], TyCtor "Int", Lit lit)
      LitString _ -> return (mempty, [], [], TyCtor "String", Lit lit)
      LitChar _ -> return (mempty, [], [], TyCtor "Char", Lit lit)
      LitBool _ -> return (mempty, [], [], TyCtor "Bool", Lit lit)

    inferApp f x = do
      (s1, cons1, env1, t1, f') <- w f
      (s2, cons2, env2, t2, x') <- local (over context $ fmap (subContextEntry s1)) $ w x
      b <- freshTyVar
      s3 <- either (throwError . review _TUnificationError) pure $ unify [(TyFun t2 b,substitute s2 t1)]
      let subs = s1 <> s2 <> s3
      return
        ( subs
        , substitute subs <$> cons1 ++ cons2
        , over (mapped._2.mapped) (substitute subs) $ env1 ++ env2
        , substitute s3 b
        , App f' x'
        )

    inferAbs x expr = do
      b <- freshTyVar
      (s1, cons, env, t1, expr') <-
        local (over context $ M.insert x (FEntry $ Forall S.empty [] b)) $ w expr
      return
        ( s1
        , cons
        , over (mapped._2.mapped) (substitute s1) env
        , TyFun (substitute s1 b) t1
        , Abs x expr'
        )

    inferLet :: MonadW r e s m => Binding Expr -> Expr -> m (Substitution Type, [Type], [Placeholder], Type, Expr)
    inferLet binding rest = case binding of
      VariableBinding x e -> do
        (s1, cons1, env1, t1, e') <- w e
        (s2, cons2, env2, t2, rest', e'') <- local (over context $ fmap (subContextEntry s1)) $ do
          env <- use tcContext
          (e'', t1') <- generalize s1 env e' cons1 env1 t1
          (s2, cons2, env2, t2, rest') <- local (over context $ M.insert x (FEntry t1')) $ w rest 
          pure (s2, cons2, env2, t2, rest', e'')
        return
          ( s1 <> s2
          , cons2
          , over (mapped._2.mapped) (substitute s2) env2
          , t2
          , Let (VariableBinding x e'') rest'
          )
      _ -> error $ "inferType: invalid binding in let: " ++ show binding

    inferRec :: MonadW r e s m => Binding Expr -> Expr -> m (Substitution Type, [Type], [Placeholder], Type, Expr)
    inferRec binding rest = case binding of
      VariableBinding name value -> do
        freshVar <- freshTyVar
        (s1, cons1, env1, t1, value') <-
          local (over context . M.insert name . REntry $ Forall S.empty [] freshVar) $ w value
        s2 <- either (throwError . review _TUnificationError) pure . unify $ (t1,freshVar) : (first TyVar <$> getSubstitution s1)
        (s3, cons2, env2, t2, rest', value'') <- local (over context $ fmap (subContextEntry s1)) $ do
          env <- use tcContext
          let replacement = foldl' App (Id name) $ fmap DictPlaceholder env1
          (value'', t1') <-
            generalize
              s1
              env
              (everywhere (replacePlaceholder replacement) value')
              cons1
              env1
              (substitute s2 t1)
          local (over context $ M.insert name $ FEntry t1') $ do
            (sub, cons, env, ty, rest') <- w rest
            pure (sub, cons, env, ty, rest', value'')
        pure
          ( s1 <> s3
          , cons2
          , over (mapped._2.mapped) (substitute s3) env2
          , t2
          , Rec (VariableBinding name value'') rest'
          )
      _ -> error $ "w: invalid binding in rec: " ++ show binding
      where
        replacePlaceholder expr (RecPlaceholder name)
          | name == bindingName binding = expr
          | otherwise = RecPlaceholder name
        replacePlaceholder _ expr = expr

    inferBranches
      :: (MonadW r s e m
         )
      => NonEmpty (Pattern,Expr)
      -> m (Substitution Type, [(Type, [Type], [Placeholder], Type, Expr)])
    inferBranches = foldrM inferBranch (mempty,[])
      where
        inferBranch (pat,branch) (subs,bTypes) = do
          (boundVars,patternType) <- patType pat
          local (over context $ M.union boundVars) $ do
            (branchSubs,preds,env,branchType,branch') <- w branch
            pure (subs <> branchSubs, (patternType, preds, env, branchType, branch'):bTypes)

    inferCase input bs = do
      (s1, cons, env, inputType, input') <- w input
      (bSubs,bs') <- inferBranches bs
      outputType <- freshTyVar
      let equations = foldr (\(p,_,_,b,_) eqs -> (p,inputType):(b,outputType):eqs) [] bs'
      subs <- either (throwError . review _TUnificationError) pure $ unify equations
      let cons' = substitute subs <$> cons ++ join (fmap (\(_, c, _, _, _) -> c) bs')
      let env' = over (mapped._2.mapped) (substitute subs) $ env ++ join (fmap (\(_, _, e, _, _) -> e) bs')
      let bs'' = N.zip (fst <$> bs) ((\(_, _, _, _, b) -> b) <$> N.fromList bs')
      pure
        ( s1 <> bSubs <> subs
        , cons'
        , env'
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

checkDefinition
  :: ( MonadFresh m
     , HasKindTable s
     , HasContext s
     , HasTypesignatures s
     , HasTcContext C.Expr s
     , MonadState s m
     , AsTypeError e
     , AsKindError e
     , MonadError e m
     )
  => Definition
  -> m (Map Identifier C.Expr, Definition)

checkDefinition def@(ValidClass supers constructor params funcs _) = do
  freshVar <- freshKindVar
  paramKinds <- for params (\param -> (,) param <$> freshKindVar)
  kindTable %= M.insert constructor (foldr KindArrow Constraint $ snd <$> paramKinds)
  table <- use kindTable
  let constructorTy = foldl' TyApp (TyCon $ TypeCon constructor) $ TyVar <$> params
  let supersTys = toTypeTyVars <$> supers
  (subs, classKind) <- flip runReaderT (M.fromList (N.toList paramKinds) `M.union` table) $ do
    subs <- checkConstraints supersTys
    local (subKindTable subs) $ do
      let freeVars =
            foldMap freeInType (S.fromList $ fmap snd funcs) `S.difference`
            foldMap freeInType (S.fromList $ constructorTy : supersTys)
      varsWithKinds <- fmap M.fromList . for (S.toList freeVars) $ \var -> (,) var <$> freshKindVar
      local (M.union varsWithKinds) $ do
        subs' <- checkSignatures $ fmap snd funcs
        (subs'', kind) <- local (fmap $ substitute subs') $ inferKind (TyCon (TypeCon constructor))
        pure (subs'' <> subs' <> subs, kind)
  kindTable %= subKindTable subs
  checkedFuncs <- for funcs $ \(name, ty) -> do
    env <- use tcContext
    (expr, checkedFuncTy) <- get >>= runReaderT (generalize mempty env (Error "Not implemented") [constructorTy] [] ty)
    context %= M.insert name (OEntry checkedFuncTy)
    pure ((name, checkedFuncTy), (name, toCoreExpr expr))
  tctxt <- use tcContext
  let tempClass = TceClass supers constructor params undefined undefined
  let superClasses = fromJust $ getAllSuperclasses (tempClass : tctxt) constructor
  let supers' = fmap getSupers superClasses
  let members = M.fromList (fst <$> checkedFuncs)
  let superMembers = getMembers <$> superClasses
  let newClass = TceClass supers' constructor params members superMembers
  tcContext %= (newClass :)
  pure
    ( M.fromList $ snd <$> checkedFuncs
    , ValidClass supers' constructor params funcs superMembers)
  where
    getMembers (TceClass _ className _ members _) = (className, fst <$> M.toList members)
    getSupers (TceClass _ className tyVars _ _) = (className, tyVars)

    checkSignatures [] = pure mempty
    checkSignatures (sig:rest) = do
      (subs, _) <- inferKind sig
      subs' <- checkSignatures rest
      pure $ subs' <> subs

checkDefinition (ValidInstance supers instHead@(InstanceHead constructor params) _ impls) = do
  tctxt <- use tcContext
  let entry = getClass tctxt constructor
  let params' = toTypeTyVars <$> params
  let constructorTy = toType (constructor, params')
  let supersTys = toTypeTyVars <$> supers
  tyVars <- M.fromList <$> traverse (\ty -> (,) ty <$> freshKindVar) (S.toList $ foldMap freeInType supersTys)
  kindTable %= M.union tyVars
  get >>= runReaderT (inferKind constructorTy)
  (superInsts, impls') <- case entry of
    Nothing -> throwError $ _NoSuchClass # constructor
    Just (TceClass classSupers _ classArgs members _)
      | let implNames = S.fromList (fmap bindingName impls)
      , let memberNames = M.keysSet members
      , let notImplemented = memberNames `S.difference` implNames
      , notImplemented /= S.empty -> throwError $ _MissingClassFunctions # (constructor, params', notImplemented)
      | otherwise -> do
          let mapping = M.fromList . N.toList $ N.zip classArgs params
          let classSupers' = over (mapped._2.mapped) (fromJust . flip M.lookup mapping) classSupers
          let fromInstHead ih = (ih ^. ihClassName, fst <$> ih ^. ihInstArgs)
          let maybeSuperInsts = getSuperInsts tctxt constructor $ fst <$> params
          case maybeSuperInsts of
            Nothing -> throwError $ _MissingSuperclassInsts # instHead
            Just superInsts -> do
              impls' <- for impls $ \(VariableBinding implName impl) ->
                case M.lookup implName members of
                  Nothing -> throwError $ _NonClassFunction # (constructor, params', implName)
                  Just (Forall _ implCons implTy) -> do
                    let inst = TceInst supers (InstanceHead constructor params) undefined
                    st <- get
                    flip runReaderT st . local (over tcContext (inst :)) $ do
                      (impl', ty) <- inferType impl
                      let subs = Substitution . N.toList $ N.zip classArgs params'
                      let implTy' = substitute subs implTy
                      let freeInImplTy' = freeInType implTy'
                      let implCons'
                            = fmap toTypeTyVars supers ++
                              filter
                                (\c -> freeInType c `S.isSubsetOf` freeInImplTy')
                                implCons
                      special ty $ Forall freeInImplTy' implCons' implTy'
                      pure $ VariableBinding implName impl'
              pure (getInstHead <$> superInsts, impls')
  let inst = TceInst supers (InstanceHead constructor params) . M.fromList $
        fmap (\(VariableBinding name expr) -> (name, toCoreExpr $ desugarExpr expr)) impls'
  tcContext %= (inst :)
  pure (M.empty, ValidInstance supers instHead superInsts impls')
  where
    getInstHead (TceInst _ ih _) = ih

checkDefinition def@(Data tyCon tyVars decls) = do
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
          env <- use tcContext
          (conExpr', conTy') <- get >>= runReaderT (generalize mempty env conExpr [] [] conTy)
          context %= M.insert dataCon (CEntry conTy')
          return (dataCon, toCoreExpr $ desugarExpr conExpr')

checkDefinition (Function (VariableBinding name expr)) = do
  maybeVar <- uses context (M.lookup name)
  case maybeVar of
    Nothing -> do
      ctxt <- use context
      (expr', ty) <- get >>= runReaderT (inferType expr)
      maybeSig <- use (typesignatures . at name)
      case maybeSig of
        Nothing -> context %= M.insert name (FEntry ty)
        Just expected -> do
          get >>= runReaderT (special ty expected)
          context %= M.insert name (FEntry expected)
      return (M.singleton name . toCoreExpr $ desugarExpr expr', Function $ VariableBinding name expr')
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

checkDefinition def = error $ "checkDefinition: invalid definition: " ++ show def

checkDefinitions ::
  ( MonadFresh m
  , HasKindTable s
  , HasContext s
  , HasTypesignatures s
  , HasTcContext C.Expr s
  , MonadState s m
  , AsTypeError e
  , AsKindError e
  , MonadError e m
  )
  => [Definition]
  -> m [Definition]
checkDefinitions defs = fmap snd <$> traverse checkDefinition defs
