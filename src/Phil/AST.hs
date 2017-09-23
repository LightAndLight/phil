module Phil.AST where

import Data.Bifunctor
import Data.Monoid

import qualified Data.Text as T

import Phil.Core.AST.Identifier

import qualified Phil.Core.AST.Binding as C
import qualified Phil.Core.AST.Definitions as C
import qualified Phil.Core.AST.Expr as C
import qualified Phil.AST.Binding as L
import qualified Phil.AST.Definitions as L
import qualified Phil.AST.Expr as L

toCore :: L.Definition -> C.Definition
toCore (L.Data name typeArgs constructors) = C.Data name typeArgs constructors
toCore (L.TypeSignature name ty) = C.TypeSignature name ty
toCore (L.Function def) = C.Function $ toCoreBinding def
toCore (L.ValidClass constraints className tyVars classMembers)
  = C.Class constraints className tyVars classMembers
toCore (L.ValidInstance constraints instHead classImpls superDicts)
  = C.Instance
      constraints
      instHead
      (fmap toCoreBinding classImpls) 
      (toCoreExpr <$> superDicts)
toCore def = error $ "toCore: invalid definition: " ++ show def

toCoreBinding :: L.Binding L.Expr -> C.Binding C.Expr
toCoreBinding (L.VariableBinding name value) = C.Binding name $ toCoreExpr value
toCoreBinding binding = error $ "toCore: invalid binding: " ++ show binding

toCoreExpr :: L.Expr -> C.Expr
toCoreExpr (L.Var name) = C.Var name
toCoreExpr (L.Lit lit) = C.Lit lit
toCoreExpr (L.Prod name vals) = C.Prod name $ fmap toCoreExpr vals
toCoreExpr (L.App f x) = C.App (toCoreExpr f) (toCoreExpr x)
toCoreExpr (L.Abs name expr) = C.Abs name $ toCoreExpr expr
toCoreExpr (L.Let binding expr) = C.Let (toCoreBinding binding) (toCoreExpr expr)
toCoreExpr (L.Rec binding expr) = C.Rec (toCoreBinding binding) (toCoreExpr expr)
toCoreExpr (L.Case expr branches) = C.Case (toCoreExpr expr) $ fmap (second toCoreExpr) branches
toCoreExpr (L.Error err) = C.Error err
toCoreExpr (L.DictVar a) = C.Var $ Left a
toCoreExpr (L.DictInst className instArgs) =
  C.Var . Left . Ident $ (T.toLower . getCtor) className <>
  foldMap getCtor instArgs
toCoreExpr (L.DictSel className expr) = C.Select (toCoreExpr expr) $ getIdent className
toCoreExpr (L.DictSuper className expr) = C.Select (toCoreExpr expr) $ getCtor className
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
