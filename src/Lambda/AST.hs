module Lambda.AST where

import Data.Bifunctor

import qualified Lambda.Core.AST.Binding as C
import qualified Lambda.Core.AST.Definitions as C
import qualified Lambda.Core.AST.Expr as C
import qualified Lambda.AST.Binding as L
import qualified Lambda.AST.Definitions as L
import qualified Lambda.AST.Expr as L
import Lambda.Sugar

toCore :: L.Definition -> C.Definition
toCore (L.Data name typeArgs constructors) = C.Data name typeArgs constructors
toCore (L.TypeSignature name ty) = C.TypeSignature name ty
toCore (L.Function def) = C.Function $ toCoreBinding def
toCore (L.ValidClass constraints className tyVars classMembers)
  = C.Class constraints className tyVars classMembers
toCore (L.ValidInstance constraints className tyArgs classImpls)
  = C.Instance constraints className tyArgs $ fmap toCoreBinding classImpls
toCore def = error $ "toCore: invalid definition: " ++ show def

toCoreBinding :: L.Binding L.Expr -> C.Binding C.Expr
toCoreBinding (L.VariableBinding name value) = C.Binding name $ toCoreExpr value
toCoreBinding binding = error $ "toCore: invalid binding: " ++ show binding

toCoreExpr :: L.Expr -> C.Expr
toCoreExpr (L.Id name) = C.Id name
toCoreExpr (L.Lit lit) = C.Lit lit
toCoreExpr (L.Prod name vals) = C.Prod name $ fmap toCoreExpr vals
toCoreExpr (L.App f x) = C.App (toCoreExpr f) (toCoreExpr x)
toCoreExpr (L.Abs name expr) = C.Abs name $ toCoreExpr expr
toCoreExpr (L.Let binding expr) = C.Let (toCoreBinding binding) (toCoreExpr expr)
toCoreExpr (L.Rec binding expr) = C.Rec (toCoreBinding binding) (toCoreExpr expr)
toCoreExpr (L.Case expr branches) = C.Case (toCoreExpr expr) $ fmap (second toCoreExpr) branches
toCoreExpr (L.Error err) = C.Error err
