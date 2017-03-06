{-# language TemplateHaskell #-}

module Lambda.Sugar
  ( AsSyntaxError(..)
  , Definition(..)
  , Expr(..)
  , FunctionDefinition(..)
  , SyntaxError(..)
  , desugar
  , desugarExpr
  ) where

import Control.Lens
import Control.Monad.Except
import           Data.Bifunctor
import           Data.Foldable
import           Data.List.NonEmpty (NonEmpty)
import qualified Data.Set           as S

import qualified Lambda.Core.AST    as C

data SyntaxError = MalformedHead C.Type
  deriving (Eq, Show)

makeClassyPrisms ''SyntaxError

-- | Naive generalization that closes over every free variable
generalize :: S.Set C.Type -> C.Type -> C.TypeScheme
generalize constraints ty
  = C.Forall (foldMap vars constraints `S.union` vars ty) constraints ty
  where
    vars (C.TyVar v) = S.singleton v
    vars (C.TyApp t t') = vars t `S.union` vars t'
    vars _ = S.empty

-- | Converts a type to the form T a_1 a_2 .. a_n, where a_i are type variables
asClassDef :: (AsSyntaxError e, MonadError e m) => C.Type -> m (C.Identifier, [C.Identifier])
asClassDef (C.TyApp (C.TyCon (C.TypeCon con)) (C.TyVar arg)) = pure (con, [arg])
asClassDef (C.TyApp left (C.TyVar arg)) = do
  (con, args) <- asClassDef left
  pure (con, args ++ [arg])
asClassDef ty = throwError $ _MalformedHead # ty

-- | Converts a type to the form T a_1 a_2 .. a_n, where a_i are any type
asClassInstance :: (AsSyntaxError e, MonadError e m) => C.Type -> m (C.Identifier, [C.Type])
asClassInstance (C.TyApp (C.TyCon (C.TypeCon con)) ty) = pure (con, [ty])
asClassInstance (C.TyApp left ty) = do
  (con, tys) <- asClassInstance left
  pure (con, tys ++ [ty])
asClassInstance ty = throwError $ _MalformedHead # ty

desugar :: (AsSyntaxError e, MonadError e m) => Definition -> m C.Definition
desugar (Data name typeArgs constructors) = pure $ C.Data name typeArgs constructors
desugar (TypeSignature name ty) = pure $ C.TypeSignature name ty
desugar (Function def) = pure . C.Function $ translateDefinition def
desugar (Class constraints classType classMembers) = do
  (className, tyVars) <- asClassDef classType
  pure . C.Class constraints className tyVars $ fmap (second $ generalize constraints) classMembers
desugar (Instance constraints classType classImpls) = do
  (className, tyArgs) <- asClassInstance classType
  pure . C.Instance constraints className tyArgs $ fmap translateDefinition classImpls

desugarExpr :: Expr -> C.Expr
desugarExpr (Id n) = C.Id n
desugarExpr (Lit l) = C.Lit l
desugarExpr (Prod name args) = C.Prod name (fmap desugarExpr args)
desugarExpr (App f x) = C.App (desugarExpr f) (desugarExpr x)
desugarExpr (Abs n expr) = C.Abs n $ desugarExpr expr
desugarExpr (Let def expr)
  = C.Let (translateDefinition def) $ desugarExpr expr
desugarExpr (Rec def expr)
  = C.Rec (translateDefinition def) $ desugarExpr expr
desugarExpr (Case n bs) = C.Case (desugarExpr n) $ fmap (fmap desugarExpr) bs
desugarExpr (Error err) = C.Error err

data Definition
  = Data C.Identifier [C.Identifier] (NonEmpty C.ProdDecl)
  | TypeSignature C.Identifier C.TypeScheme
  | Function FunctionDefinition
  | Class (S.Set C.Type) C.Type [(C.Identifier, C.Type)]
  | Instance (S.Set C.Type) C.Type [FunctionDefinition]

data Expr
  = Id C.Identifier
  | Lit C.Literal
  | Prod C.Identifier [Expr]
  | App Expr Expr
  | Abs C.Identifier Expr
  | Let FunctionDefinition Expr
  | Rec FunctionDefinition Expr
  | Case Expr (NonEmpty (C.Pattern,Expr))
  | Error String

data FunctionDefinition = FunctionDefinition C.Identifier [C.Identifier] Expr

translateDefinition :: FunctionDefinition -> C.Binding
translateDefinition (FunctionDefinition name args expr) = C.Binding name $ foldr C.Abs (desugarExpr expr) args
