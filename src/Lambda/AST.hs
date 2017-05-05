module Lambda.AST where

import Control.Monad.Reader
import Control.Lens
import Data.Bifunctor
import Data.Char
import Data.Foldable

import Lambda.Core.AST.Identifier
import Lambda.AST.Modules
import Lambda.AST.Modules.ModuleName
import Lambda.ModuleInfo
import Lambda.Sugar

import qualified Lambda.Core.AST.Binding as C
import qualified Lambda.Core.AST.Definitions as C
import qualified Lambda.Core.AST.Expr as C
import qualified Lambda.AST.Binding as L
import qualified Lambda.AST.Definitions as L
import qualified Lambda.AST.Expr as L

toCore
  :: ( HasModuleInfo r
     , MonadReader r m
     )
  => L.Definition
  -> m C.Definition
toCore (L.Data name typeArgs constructors) = pure $ C.Data name typeArgs constructors
toCore (L.TypeSignature name ty) = pure $ C.TypeSignature name ty
toCore (L.Function def) = C.Function <$> toCoreBinding def
toCore (L.ValidClass constraints className tyVars classMembers)
  = pure $ C.Class constraints className tyVars classMembers
toCore (L.ValidInstance constraints instHead classImpls superDicts)
  = C.Instance constraints instHead <$>
      traverse toCoreBinding classImpls <*>
      traverse toCoreExpr superDicts
toCore def = error $ "toCore: invalid definition: " ++ show def

toCoreBinding
  :: ( HasModuleInfo r
     , MonadReader r m
     )
  => L.Binding L.Expr
  -> m (C.Binding C.Expr)
toCoreBinding (L.VariableBinding name value) = C.Binding name <$> toCoreExpr value
toCoreBinding binding = error $ "toCore: invalid binding: " ++ show binding

eraseModuleName
  :: ( HasModuleInfo r
     , MonadReader r m
     )
  => Maybe ModuleName
  -> Identifier
  -> m C.Expr
eraseModuleName modName name = do
  currentModName <- view (moduleInfo.miModuleName)
  pure $ if Just currentModName == modName
    then C.Id Nothing name
    else C.Id modName name

toCoreExpr :: (HasModuleInfo r, MonadReader r m) => L.Expr -> m C.Expr
toCoreExpr (L.Id modName name) = eraseModuleName modName name
toCoreExpr (L.Lit lit) = pure $ C.Lit lit
toCoreExpr (L.Prod name vals) = C.Prod name <$> traverse toCoreExpr vals
toCoreExpr (L.App f x) = C.App <$> toCoreExpr f <*> toCoreExpr x
toCoreExpr (L.Abs name expr) = C.Abs name <$> toCoreExpr expr
toCoreExpr (L.Let binding expr) = C.Let <$> toCoreBinding binding <*> toCoreExpr expr
toCoreExpr (L.Rec binding expr) = C.Rec <$> toCoreBinding binding <*> toCoreExpr expr
toCoreExpr (L.Case expr branches) = C.Case <$> toCoreExpr expr <*> traverseOf (traversed._2) toCoreExpr branches
toCoreExpr (L.Error err) = pure $ C.Error err
toCoreExpr (L.DictVar modName a) = eraseModuleName modName a
toCoreExpr (L.DictInst modName className instArgs) = eraseModuleName modName $ fmap toLower className ++ fold instArgs
toCoreExpr (L.DictSel className expr) = C.Select <$> toCoreExpr expr <*> pure className
toCoreExpr (L.DictSuper className expr) = C.Select <$> toCoreExpr expr <*> pure className
toCoreExpr expr = error $ "toCoreExpr: invalid argument: " ++ show expr

everywhere :: (L.Expr -> L.Expr) -> L.Expr -> L.Expr
everywhere f (L.Prod name vals) = L.Prod name $ everywhere f <$> vals
everywhere f (L.App func arg) = L.App (everywhere f func) (everywhere f arg)
everywhere f (L.Abs name expr) = L.Abs name $ everywhere f expr
everywhere f (L.Let binding rest) = L.Let (everywhere f <$> binding) (everywhere f rest)
everywhere f (L.Rec binding rest) = L.Rec (everywhere f <$> binding) (everywhere f rest)
everywhere f (L.Case expr branches) = L.Case (everywhere f expr) (second (everywhere f) <$> branches)
everywhere f (L.DictSel className expr) = L.DictSel className $ everywhere f expr
everywhere f (L.DictSuper className expr) = L.DictSuper className $ everywhere f expr
everywhere f e = f e

everywhereM :: Applicative m => (L.Expr -> m L.Expr) -> L.Expr -> m L.Expr
everywhereM f (L.Prod name vals) = L.Prod name <$> traverse (everywhereM f) vals
everywhereM f (L.App func arg) = L.App <$> everywhereM f func <*> everywhereM f arg
everywhereM f (L.Abs name expr) = L.Abs name <$> everywhereM f expr
everywhereM f (L.Let binding rest) = L.Let <$> traverse (everywhereM f) binding <*> everywhereM f rest
everywhereM f (L.Rec binding rest) = L.Rec <$> traverse (everywhereM f) binding <*> everywhereM f rest
everywhereM f (L.Case expr branches) = L.Case <$> everywhereM f expr <*> traverse (traverse $ everywhereM f) branches
everywhereM f (L.DictSel className expr) = L.DictSel className <$> everywhereM f expr
everywhereM f (L.DictSuper className expr) = L.DictSuper className <$> everywhereM f expr
everywhereM f e = f e
