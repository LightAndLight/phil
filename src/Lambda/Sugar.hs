{-# language TemplateHaskell #-}
{-# language DeriveFunctor #-}

module Lambda.Sugar
  ( AsSyntaxError(..)
  , SyntaxError(..)
  , asClassDef
  , asClassInstance
  , desugar
  , desugarBinding
  , desugarExpr
  ) where

import Control.Lens
import Control.Monad.Except
import           Data.Bifunctor
import           Data.Foldable
import           Data.List.NonEmpty (NonEmpty)
import qualified Data.Set           as S

import qualified Lambda.AST.Binding as L
import qualified Lambda.AST.Definitions as L
import qualified Lambda.AST.Expr as L
import qualified Lambda.Core.AST.Binding as C
import qualified Lambda.Core.AST.Definitions    as C
import qualified Lambda.Core.AST.Expr    as C
import Lambda.Core.AST.Identifier
import Lambda.Core.AST.Literal
import Lambda.Core.AST.Types
import Lambda.Core.AST.Pattern
import Lambda.Core.AST.ProdDecl

data SyntaxError = MalformedHead Type
  deriving (Eq, Show)

makeClassyPrisms ''SyntaxError

-- | Naive generalization that closes over every free variable
generalize :: [Type] -> Type -> TypeScheme
generalize constraints ty
  = Forall (foldMap vars constraints `S.union` vars ty) constraints ty
  where
    vars (TyVar v) = S.singleton v
    vars (TyApp t t') = vars t `S.union` vars t'
    vars _ = S.empty

-- | Converts a type to the form T a_1 a_2 .. a_n, where a_i are type variables
asClassDef :: (AsSyntaxError e, MonadError e m) => Type -> m (Identifier, [Identifier])
asClassDef (TyApp (TyCon (TypeCon con)) (TyVar arg)) = pure (con, [arg])
asClassDef (TyApp left (TyVar arg)) = do
  (con, args) <- asClassDef left
  pure (con, args ++ [arg])
asClassDef ty = throwError $ _MalformedHead # ty

-- | Converts a type to the form T a_1 a_2 .. a_n, where a_i are any type
asClassInstance :: (AsSyntaxError e, MonadError e m) => Type -> m (Identifier, [Type])
asClassInstance (TyApp (TyCon (TypeCon con)) ty) = pure (con, [ty])
asClassInstance (TyApp left ty) = do
  (con, tys) <- asClassInstance left
  pure (con, tys ++ [ty])
asClassInstance ty = throwError $ _MalformedHead # ty

desugar :: (AsSyntaxError e, MonadError e m) => L.Definition -> m L.Definition
desugar (L.Function def) = pure . L.Function $ desugarBinding def
desugar (L.Class constraints classType classMembers) = do
  (className, tyVars) <- asClassDef classType
  pure $ L.ValidClass constraints className tyVars classMembers
desugar (L.Instance constraints classType classImpls) = do
  (className, tyArgs) <- asClassInstance classType
  unless (all (sameConstructor className) constraints) . throwError $ _MalformedHead # classType
  pure . L.ValidInstance constraints className tyArgs $ fmap desugarBinding classImpls
  where
    sameConstructor name (TyApp (TyCon (TypeCon name')) _) = name == name'
    sameConstructor _ _ = False
desugar def = pure def

desugarExpr :: L.Expr -> L.Expr
desugarExpr (L.Prod name args) = L.Prod name (fmap desugarExpr args)
desugarExpr (L.App f x) = L.App (desugarExpr f) (desugarExpr x)
desugarExpr (L.Abs n expr) = L.Abs n $ desugarExpr expr
desugarExpr (L.Let def expr)
  = L.Let (desugarBinding def) $ desugarExpr expr
desugarExpr (L.Rec def expr)
  = L.Rec (desugarBinding def) $ desugarExpr expr
desugarExpr (L.Case n bs) = L.Case (desugarExpr n) $ fmap (fmap desugarExpr) bs
desugarExpr expr = expr

desugarBinding :: L.Binding L.Expr -> L.Binding L.Expr
desugarBinding (L.FunctionBinding name args expr) = L.VariableBinding name $ foldr L.Abs (desugarExpr expr) args
desugarBinding binding = binding
