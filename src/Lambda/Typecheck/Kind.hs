module Lambda.Typecheck.Kind where

inferKind :: AsKindError e => Type -> TC e (Substitution Kind, Kind)
inferKind (TyVar var) = do
  kind <- lookupKind var =<< view kindTable
  pure (mempty, kind)
inferKind (TyApp con arg) = do
  (s1,conKind) <- inferKind con
  (s2,argKind) <- local (over kindTable $ fmap (substitute s1)) $ inferKind arg
  returnKind <- freshKindVar
  case unify [(substitute s2 conKind,KindArrow argKind returnKind)] of
    Right s3 -> pure (s3 <> s2 <> s1, substitute s3 returnKind)
    Left err -> throwError $ _KUnificationError # err
inferKind (TyCon tyCon) = case tyCon of
  FunCon -> pure (mempty, KindArrow Star $ KindArrow Star Star)
  TypeCon con -> do
    kind <- lookupKind con =<< view kindTable
    pure (mempty, kind)

checkDefinitionKinds
  :: AsKindError e
  => Identifier
  -> [Identifier]
  -> NonEmpty ProdDecl
  -> TC e Kind
checkDefinitionKinds tyCon tyVars prods = do
  kinds <- traverse (const freshKindVar) tyVars
  let constructorKind = foldr KindArrow Star kinds
  let update = M.insert tyCon constructorKind . M.union (M.fromList $ zip tyVars kinds)
  subs <- local (over kindTable update) . checkConstructors $ N.toList prods
  pure . instantiateKind $ substitute subs constructorKind
  where
    checkConstructors [] = pure mempty
    checkConstructors (ProdDecl _ argTys:rest) = do
      subs <- checkArgs argTys
      liftA2 (<>) (local (over kindTable $ fmap (substitute subs)) (checkConstructors rest)) (pure subs)

    checkArgs [] = pure mempty
    checkArgs (argTy:rest) = do
      (subs, kind) <- inferKind argTy
      case unify [(kind, Star)] of
        Right subs' -> do
          let subs'' = subs' <> subs
          liftA2 (<>) (local (over kindTable $ fmap (substitute subs'')) (checkArgs rest)) (pure subs'')
        Left err -> throwError $ _KUnificationError # err
