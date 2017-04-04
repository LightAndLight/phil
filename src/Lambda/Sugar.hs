{-# language TemplateHaskell #-}
{-# language DeriveFunctor #-}

module Lambda.Sugar
  ( AsSyntaxError(..)
  , SyntaxError(..)
  , asClassDef
  , asClassInstance
  , asClassInstanceP
  , desugar
  , desugarBinding
  , desugarExpr
  ) where

import Control.Lens
import Control.Monad.Except
import           Data.Bifunctor
import           Data.Foldable
import           Data.List.NonEmpty (NonEmpty(..))
import           Data.Semigroup
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
import Lambda.Typeclasses

data SyntaxError
  = MalformedHead Type
  | InvalidInstanceArg Type
  | NoInstanceArgs Type
  | InvalidClassArg Type
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
asClassDef :: (AsSyntaxError e, MonadError e m) => Type -> m (Identifier, NonEmpty Identifier)
asClassDef (TyApp (TyCon (TypeCon con)) (TyVar arg)) = pure (con, arg :| [])
asClassDef (TyApp left (TyVar arg)) = do
  (con, args) <- asClassDef left
  pure (con, args <> pure arg)
asClassDef ty = throwError $ _InvalidClassArg # ty

-- | Converts a 'Type' to a valid instance head, or throws a 'SyntaxError'
-- | if it isn't
asClassInstance
  :: (AsSyntaxError e, MonadError e m)
  => Type
  -> m InstanceHead
asClassInstance ty = go ty
  where
    go (TyApp (TyCtor className) arg) = do
      res <- ctorAndTyVars arg
      pure $ InstanceHead className (pure res)
    go (TyApp left arg) = do
      res <- ctorAndTyVars arg
      instHead <- go left
      pure (instHead & over ihInstArgs (<> pure res))
    go _ = throwError $ _NoInstanceArgs # ty

    ctorAndTyVars ty' = case ty' of
      TyCtor con -> pure (con, []) 
      TyApp rest (TyVar var) -> do
        (con, vars) <- ctorAndTyVars rest
        pure (con, vars ++ [var])
      _ -> throwError $ _InvalidInstanceArg # ty

-- | Converts a type to the form T a_1 a_2 .. a_n, where a_i are any type
-- |
-- | Partial
asClassInstanceP :: Type -> InstanceHead
asClassInstanceP ty
  = case asClassInstance ty :: Either SyntaxError InstanceHead of
      Right res -> res
      Left _ -> error $ "asClassInstanceP: invalid argument: " ++ show ty 

desugar :: (AsSyntaxError e, MonadError e m) => L.Definition -> m L.Definition
desugar (L.Function def) = pure . L.Function $ desugarBinding def
desugar (L.Class constraints classType classMembers) = do
  (className, tyVars) <- asClassDef classType
  pure $ L.ValidClass constraints className tyVars classMembers
desugar (L.Instance constraints classType classImpls) = do
  InstanceHead className tyArgs <- asClassInstance classType
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
