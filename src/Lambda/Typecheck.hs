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
import           Data.Map             (Map)
import           Data.Maybe
import           Data.Monoid
import           Data.Set             (Set)
import           Data.Traversable

import qualified Data.List.NonEmpty   as N
import qualified Data.Map             as M
import qualified Data.Set             as S

import           Lambda.AST (everywhere, toCoreExpr)
import           Lambda.AST.Binding
import           Lambda.AST.Definitions
import           Lambda.AST.Expr
import           Lambda.AST.Modules.ModuleName
import           Lambda.Core.AST.Identifier
import           Lambda.Core.AST.InstanceHead
import           Lambda.Core.AST.Lens
import           Lambda.Core.AST.Literal
import           Lambda.Core.AST.Types
import           Lambda.Core.AST.Pattern
import           Lambda.Core.AST.ProdDecl
import Lambda.Core.Kinds.KindError
import Lambda.ModuleInfo
import Lambda.Sugar (asClassInstanceP, desugarExpr)
import Lambda.Typecheck.Entailment
import Lambda.Typecheck.TC
import Lambda.Typecheck.TypeError
import Lambda.Typecheck.Unification
import Lambda.Typeclasses

import           qualified Lambda.Core.AST.Expr as C

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
  :: Substitution Type -- ^ Substitutions to apply to placeholders
  -> [TypeclassEntry a] -- ^ Typeclass environment
  -> Expr -- ^ Expression to operate on
  -> [Type] -- ^ Constraints
  -> Type -- ^ Type to generalize
  -> m (Expr, TypeScheme)
generalize subs tcenv expr cons ty = do
  freeInCtxt <- freeInContext
  let frees = (freeInType ty `S.union` foldMap freeInType cons)
        `S.difference` freeInCtxt

  moduleInfo <- getModuleInfo
  simplCons <- runReaderT (simplify tcenv cons) moduleInfo

  let expr' = everywhere (subPlaceholders subs) expr

  let placeholders
        = ctorAndArgs <$> simplCons :: [(Identifier, [Type])]

  (deferred, dictVars, expr'') <-
    resolveAllPlaceholders
      False
      tcenv
      freeInCtxt
      (flip (,) Nothing . second N.fromList <$> placeholders)
      expr'

  let finalCons = filter ((S.empty /=) . freeInType) simplCons

  pure (foldr Abs expr'' dictVars, Forall frees finalCons ty)
  where

    fromDictVar (DictVar _ a) as = a : as
    fromDictVar _ as = as

freshTyVar :: (MonadFresh m, HasKindTable s, MonadState s m) => m Type
freshTyVar = do
  name <- ("t" ++) <$> fresh
  updateKindTable <- M.insert name <$> freshKindVar
  kindTable %= updateKindTable
  return $ TyVar name

instantiate :: TypeScheme -> TC e ([Type], Type)
instantiate (Forall vars cons ty) = do
  subs <- Substitution <$> for (S.toList vars) makeFreshVar
  pure (fmap (substitute subs) cons, substitute subs ty)
  where
    makeFreshVar var = do
      var' <- freshTyvar
      if TyVar var == var'
        then makeFreshVar var
        else pure (var, var')

kindPreservingSubstitution :: AsKindError e => Substitution Type -> TC e ()
kindPreservingSubstitution subs = go $ getSubstitution subs
  where
    go [] = pure ()
    go ((name, targetType):rest) = do
      kind <- lookupKind name
      case targetType of
        TyVar name' -> do
          kind' <- lookupKind name' table
          either (tcError . review _KUnificationError) (const $ go rest) $ unify [(kind, kind')]
        _ -> go rest

-- Checks that the second argument is more special that the first
special
  :: ( MonadFresh m
     , AsTypeError e
     , AsKindError e
     , MonadError e m
     , HasKindTable s
     , MonadState s m
     , HasModuleInfo r
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

    allEntails <- and <$> traverse (entails tctxt cons') consSubbed
    unless allEntails . throwError $ _CouldNotDeduce # (consSubbed, cons')
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

newtype TypeOrKindError
  = TypeOrKindError
  { getTOKError :: Either TypeError KindError
  }

instance AsTypeError TypeOrKindError where
  _TypeError = prism' (TypeOrKindError . Left) $
    \s -> case getTOKError s of
      Left a -> Just a
      _ -> Nothing

instance AsKindError TypeOrKindError where
  _KindError = prism' (TypeOrKindError . Right) $
    \s -> case getTOKError s of
      Right a -> Just a
      _ -> Nothing

runInferTypeScheme
  :: ModuleName
  -> Expr
  -> Either TypeOrKindError (Expr, TypeScheme)
runInferTypeScheme modName
  = runExcept .
    runFreshT .
    flip evalStateT (initialInferenceState modName) .
    flip runReaderT (initialInferenceState modName) .
    inferTypeScheme

type MonadW r s e m
  = ( MonadFresh m
    , HasKindTable s
    , HasTcContext C.Expr s
    , MonadState s m
    , HasModuleInfo r
    , MonadReader r m
    , AsTypeError e
    , AsKindError e
    , MonadError e m
    )

patType ::
  ( MonadFresh m
  , HasKindTable s
  , MonadState s m
  , HasModuleInfo r
  , HasContext r
  , MonadReader r m
  , AsTypeError e
  , MonadError e m
  )
  => Pattern
  -> m (Map Identifier ContextEntry,Type)
patType (PatId name) = do
  ty <- freshTyVar
  entry <- addFEntry name (Forall S.empty [] ty) M.empty
  return (entry, ty)
patType (PatCon conName args) = do
  (_,conTy) <- instantiate . typeScheme =<< lookupId conName
  let (retTy,argTys) = conArgTypes conTy
      actualArgs = length args
      expectedArgs = length argTys
  when (actualArgs /= expectedArgs) .
    throwError $ _PatternArgMismatch # (conName, actualArgs, expectedArgs)
  modName <- view (moduleInfo.miModuleName)
  boundVars <- foldrM (\(arg,argTy) -> addFEntry arg (Forall S.empty [] argTy)) M.empty $ zip args argTys
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
     )
  => ModuleName
  -> Map Identifier ContextEntry -- ^ Context
  -> Expr -- ^ Expression to type
  -> m (Expr, TypeScheme)
runWithContext moduleName ctxt
  = runFreshT .
    flip evalStateT (initialInferenceState moduleName) .
    flip runReaderT (initialInferenceState moduleName)
      { _isContext = ctxt } .
    inferTypeScheme

inferType
  :: (MonadW r s e m)
  => Map Identifier ContextEntry
  -> Expr -- ^ Target expression
  -> m (Substitution Type, [Type], [Placeholder], Type, Expr)
inferType ctxt e = case e of
  Error _ -> (,,,,) mempty [] [] <$> freshTyVar <*> pure e
  Id modName name -> inferIdent modName name
  Lit lit -> inferLiteral lit
  App f x -> inferApp f x
  Abs x expr -> inferAbs x expr
  Let binding rest -> inferLet binding rest
  Rec binding rest -> inferRec binding rest
  Case input bs -> inferCase input bs
  _ -> error $ "inferType: invalid expression: " ++ show e
  where
    consToPlaceholders [] = pure ([], [])
    consToPlaceholders (cons : rest)
      = let (className, instArgs) = ctorAndArgs cons
        in bimap
            (DictPlaceholder (className, N.fromList instArgs) :)
            ((className, N.fromList instArgs) :)
            <$> consToPlaceholders rest

    inferIdent
      :: MonadW r e s m
      => Maybe ModuleName
      -> Identifier
      -> m (Substitution Type, [Type], [Placeholder], Type, Expr)
    inferIdent modName name = do
      entry <- lookupId name
      case entryType entry of
        OEntry -> do
          ([cons], ty) <- instantiate $ typeScheme entry
          ([placeholder], env) <- consToPlaceholders [cons]
          pure
            ( mempty
            , [cons]
            , env
            , ty
            , DictSel name placeholder
            )
        REntry -> do
          (cons, ty) <- instantiate $ typeScheme entry
          (placeholders, env) <- consToPlaceholders cons
          pure
            ( mempty
            , cons
            , env
            , ty
            , RecPlaceholder name
            )
        _ -> do
          case modName of
            Just modName
              | locality entry /= modName
              -> error "inferType: same identifer name but different modules"
              | otherwise -> pure ()
            _ -> pure ()
          (cons, ty) <- instantiate $ typeScheme entry
          (placeholders, env) <- consToPlaceholders cons
          pure
            ( mempty
            , cons
            , env
            , ty
            , foldl' App (Id (Just $ locality entry) name) placeholders
            )

    inferLiteral lit = case lit of
      LitInt _ -> return (mempty, [], [], TyCtor "Int", Lit lit)
      LitString _ -> return (mempty, [], [], TyCtor "String", Lit lit)
      LitChar _ -> return (mempty, [], [], TyCtor "Char", Lit lit)
      LitBool _ -> return (mempty, [], [], TyCtor "Bool", Lit lit)

    inferApp f x = do
      (s1, cons1, env1, t1, f') <- inferType ctxt f
      (s2, cons2, env2, t2, x') <- inferType (subContextEntry s1 <$> ctxt) x
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
      modName <- view (moduleInfo.miModuleName)
      let ctxt' = M.insert x . ContextEntry modName FEntry $ Forall S.empty [] b
      (s1, cons, env, t1, expr') <- inferType ctxt' expr
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
        (s1, cons1, env1, t1, e') <- inferType ctxt e
        let ctxt' = fmap (subContextEntry s1) ctxt
        (s2, cons2, env2, t2, rest', e'') <- do
          env <- use tcContext
          (e'', t1') <- ask >>= generalize s1 env e' cons1 t1
          modName <- view (moduleInfo.miModuleName)
          (s2, cons2, env2, t2, rest') <- local (over context . M.insert x $ ContextEntry modName FEntry t1') $ inferType rest 
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
        modName <- view (moduleInfo.miModuleName)
        (s1, cons1, env1, t1, value') <-
          local (over context . M.insert name $ ContextEntry modName REntry $ Forall S.empty [] freshVar) $ inferType value
        s2 <- either (throwError . review _TUnificationError) pure . unify $ (t1,freshVar) : (first TyVar <$> getSubstitution s1)
        (s3, cons2, env2, t2, rest', value'') <- local (over context $ fmap (subContextEntry s1)) $ do

          let replacement = foldl' App (Id Nothing name) $
                fmap (DictPlaceholder . over (_2.mapped) (substitute s2)) env1

          tcenv <- use tcContext
          (value'', t1') <-
            ask >>=
            generalize
              s1
              tcenv
              (everywhere (subPlaceholders s2 . replacePlaceholder replacement) value')
              (substitute s2 <$> cons1)
              (substitute s2 t1)
          modName <- view (moduleInfo.miModuleName)
          local (over context . M.insert name $ ContextEntry modName FEntry t1') $ do
            (sub, cons, env, ty, rest') <- inferType rest
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
            (branchSubs,preds,env,branchType,branch') <- inferType branch
            pure (subs <> branchSubs, (patternType, preds, env, branchType, branch'):bTypes)

    inferCase input bs = do
      (s1, cons, env, inputType, input') <- inferType input
      (bSubs,bs') <- inferBranches bs
      outputType <- freshTyVar
      let equations = foldr (\(p,_,_,b,_) eqs -> (inputType,p):(outputType,b):eqs) [] bs'
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

inferTypeScheme :: (MonadW r s e m, HasTcContext C.Expr s) => Expr -> m (Expr, TypeScheme)
inferTypeScheme e = do
  (subs, cons, dictParams, ty, e') <- inferType e
  env <- use tcContext
  ask >>= generalize subs env (everywhere (subPlaceholders subs) e') (substitute subs <$> cons) (substitute subs ty)
