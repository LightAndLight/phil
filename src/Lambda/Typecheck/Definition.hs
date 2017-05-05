{-# language FlexibleContexts #-}

module Lambda.Typecheck.Definition where

import Control.Applicative
import Control.Lens
import Control.Monad.Except
import Control.Monad.Fresh
import Control.Monad.Reader
import Control.Monad.State
import Data.Bifunctor
import Data.Foldable
import Data.Maybe
import Data.Monoid
import Data.List.NonEmpty (NonEmpty)
import Data.Map (Map)
import Data.Traversable

import qualified Data.List.NonEmpty as N
import qualified Data.Map as M
import qualified Data.Set as S

import Lambda.AST
import Lambda.AST.Binding
import Lambda.AST.Definitions
import Lambda.AST.Expr
import Lambda.Core.AST.Identifier
import Lambda.Core.AST.InstanceHead
import Lambda.Core.AST.ProdDecl
import Lambda.Core.AST.Types
import Lambda.Core.Kinds
import Lambda.ModuleInfo
import Lambda.Sugar
import Lambda.Typeclasses
import Lambda.Typecheck
import Lambda.Typecheck.Entailment
import Lambda.Typecheck.TypeError
import Lambda.Typecheck.Unification

import qualified Lambda.Core.AST.Expr as C

-- | Created a function for the specified ADT constructor
buildDataCon :: ProdDecl -> Expr
buildDataCon (ProdDecl dataCon argTys)
  = let (args, expr) = go (take (length argTys) (mappend "a" . show <$> [1..]))
    in expr $ Prod dataCon args
  where
    go [] = ([], id)
    go (var:vars) = bimap (Id Nothing var :) (Abs var <$>) $ go vars

checkDefinition
  :: ( HasModuleInfo r
     , MonadReader r m
     , MonadFresh m
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

checkDefinition def@(ValidClass supers constructor params funcs) = do
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
    (expr, checkedFuncTy) <- get >>= generalize mempty env (Error "Not implemented") [constructorTy] ty
    modName <- view (moduleInfo.miModuleName)
    context %= M.insert name (ContextEntry modName OEntry checkedFuncTy)
    expr' <- toCoreExpr expr
    pure ((name, checkedFuncTy), (name, expr'))
  tctxt <- use tcContext
  let members = M.fromList (fst <$> checkedFuncs)
  let newClass = TceClass supers constructor params members
  tcContext %= (newClass :)
  pure
    ( M.fromList $ snd <$> checkedFuncs
    , ValidClass supers constructor params funcs
    )
  where
    getMembers (TceClass _ className _ members) = (className, fst <$> M.toList members)
    getSupers (TceClass _ className tyVars _) = (className, tyVars)

    checkSignatures [] = pure mempty
    checkSignatures (sig:rest) = do
      (subs, _) <- inferKind sig
      subs' <- checkSignatures rest
      pure $ subs' <> subs

checkDefinition (ValidInstance supers instHead@(InstanceHead constructor params) impls _) = do
  tctxt <- use tcContext
  let params' = toTypeTyVars <$> params
  let constructorTy = toType (constructor, params')
  let supersTys = toTypeTyVars <$> supers
  tyVars <- M.fromList <$> traverse (\ty -> (,) ty <$> freshKindVar) (S.toList $ foldMap freeInType supersTys)
  kindTable %= M.union tyVars
  get >>= runReaderT (inferKind constructorTy)
  TceClass classSupers _ classArgs members <- tryGetClass tctxt constructor

  let mapping = M.fromList . N.toList $ N.zip classArgs params
  let classSupers' = over (mapped._2.mapped) (fromJust . flip M.lookup mapping) classSupers

  classSuperInsts <- traverse (uncurry $ tryGetInst tctxt) classSupers'
     
  modName <- view (moduleInfo.miModuleName)
  let supersPlaceholders =
        zip (over (mapped._2.mapped) TyVar supers) $
        Just . DictVar Nothing . ("dict" ++) . fst <$> supers

  checkAllMembersImplemented members impls

  impls' <- for impls $ \(VariableBinding implName impl) -> do
    Forall _ implCons implTy <- tryGetImpl constructor params' implName members 
    let inst = TceInst modName supers (InstanceHead constructor params) undefined
    st <- get
    flip runReaderT st . local (over tcContext (inst :)) $ do
      (_, ty) <- inferTypeScheme impl
      let subs = Substitution . N.toList $ N.zip classArgs params'
      let implTy' = substitute subs implTy
      let freeInImplTy' = freeInType implTy'
      let implCons'
            = fmap toTypeTyVars supers ++
              filter
                (\c -> freeInType c `S.isSubsetOf` freeInImplTy')
                implCons
      special ty $ Forall freeInImplTy' implCons' implTy'
      tctxt <- view tcContext
      (_, cons, _, ty, impl') <- inferType impl
      let subs = findMatchingCons (toTypeTyVars <$> supers) cons
      (_, dictVars, impl'') <-
        resolveAllPlaceholders
          True
          tctxt
          S.empty
          (flip (,) Nothing . second N.fromList . ctorAndArgs <$> cons)
          (everywhere (subPlaceholders subs) impl')
      (_, _, impl''') <-
        resolveAllPlaceholders
          False
          tctxt
          S.empty
          supersPlaceholders
          impl''
      pure $ VariableBinding implName $ foldr Abs impl''' dictVars

  inst <- TceInst modName supers (InstanceHead constructor params) .
          M.fromList <$>
          traverse (\(VariableBinding name expr) -> (,) name <$> toCoreExpr (desugarExpr expr)) impls'

  supersDicts <- traverse (buildSuperDicts tctxt supersPlaceholders) classSuperInsts

  tcContext %= (inst :)
  pure (M.empty, ValidInstance supers instHead impls' supersDicts)

  where
    checkAllMembersImplemented members impls = do
      let implNames = S.fromList (fmap bindingName impls)
      let memberNames = M.keysSet members
      let notImplemented = memberNames `S.difference` implNames
      when (notImplemented /= S.empty) . throwError $
        _MissingClassFunctions # (constructor, params, notImplemented)

    buildSuperDicts tctxt placeholders (TceInst _ _ (InstanceHead className instArgs) _)
      = fromJust . snd <$>
        resolvePlaceholder
          False
          tctxt
          S.empty
          placeholders
          (className, toTypeTyVars <$> instArgs) 
  
    -- | Find a substitution that will rewrite a member's inferred
    -- | constraints in terms of the instance's parameters
    findMatchingCons
      :: [Type] -- ^ Instance superclass constraints
      -> [Type] -- ^ Class member constraints
      -> Substitution Type
    findMatchingCons [] cons = mempty
    findMatchingCons (con : rest) cons
      = case go con cons of
          Just (sub, rest') -> sub <> findMatchingCons rest rest'
          Nothing -> findMatchingCons rest cons
      where
        go con [] = Nothing
        go con (con' : rest) = case unify [(con', con)] of
          Right sub -> Just (sub, rest)
          Left _ -> second (con' :) <$> go con rest

    tryGetClass :: (AsTypeError e, MonadError e m) => [TypeclassEntry a] -> Identifier -> m (TypeclassEntry a)
    tryGetClass tctxt cons
      = maybe
          (throwError $ _NoSuchClass # cons)
          pure
          (getClass tctxt cons)

    tryGetInst
      :: (AsTypeError e, MonadError e m)
      => [TypeclassEntry a]
      -> Identifier
      -> NonEmpty (Identifier, [Identifier])
      -> m (TypeclassEntry a)
    tryGetInst tctxt targetCons targetParams
      = maybe 
          (throwError $ _MissingSuperclassInst #
              ((constructor, params), (targetCons, targetParams)))
          pure
          (getInst tctxt targetCons $ fst <$> targetParams)

    tryGetImpl :: (AsTypeError e, MonadError e m) => Identifier -> NonEmpty Type -> Identifier -> Map Identifier TypeScheme -> m TypeScheme
    tryGetImpl cons params implName members
      = maybe
          (throwError $ _NonClassFunction # (cons, implName))
          pure
          (M.lookup implName members)
          

checkDefinition def@(Data tyCon tyVars decls) = do
  table <- use kindTable
  kind <- runReaderT (checkDefinitionKinds tyCon tyVars decls) table
  kindTable %= M.insert tyCon kind
  let tyVars' = fmap TyVar tyVars
  liftA2 (,) (M.fromList <$> traverse (checkDataDecl tyCon tyVars') (N.toList decls)) $ pure def
  where
    checkDataDecl
      :: ( Monad m )
      => Identifier
      -> [Type]
      -> ProdDecl
      -> m (Identifier, C.Expr)
    checkDataDecl tyCon tyVars p@(ProdDecl dataCon argTys) = do
      maybeCon <- use (context . at dataCon)
      case maybeCon of
        Just _ -> throwError $ _AlreadyDefined # dataCon
        Nothing -> do
          let conTy = flip (foldr TyFun) argTys $ foldl' TyApp (TyCon $ TypeCon tyCon) tyVars
          ctxt <- use context
          let conExpr = buildDataCon p
          env <- use tcContext
          (conExpr', conTy') <- get >>= generalize mempty env conExpr [] conTy
          modName <- view (moduleInfo.miModuleName)
          context %= M.insert dataCon (ContextEntry modName CEntry conTy')
          (,) dataCon <$> toCoreExpr (desugarExpr conExpr')

checkDefinition (Function (VariableBinding name expr)) = do
  maybeVar <- uses context (M.lookup name)
  case maybeVar of
    Nothing -> do
      ctxt <- use context
      (expr', ty) <- get >>= runReaderT (inferTypeScheme $ desugarExpr expr)
      maybeSig <- use (typesignatures . at name)
      modName <- view (moduleInfo.miModuleName)
      case maybeSig of
        Nothing -> context %= M.insert name (ContextEntry modName FEntry ty)
        Just expected -> do
          get >>= runReaderT (special ty expected)
          context %= M.insert name (ContextEntry modName FEntry expected)
      expr'' <- toCoreExpr expr'
      pure (M.singleton name expr'', Function $ VariableBinding name expr')
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
  ( HasModuleInfo r
  , MonadReader r m
  , MonadFresh m
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
