{-# language TemplateHaskell #-}

module Lambda.Sugar
  ( AsSyntaxError(..)
  , Definition(..)
  , Expr(..)
  , FunctionDefinition(..)
  , SyntaxError(..)
  , C.ProdDecl(..)
  , asClassDef
  , asClassInstance
  , desugar
  , desugarExpr
  ) where

import Control.Lens
import Control.Monad.Except
import           Data.Bifunctor
import           Data.Foldable
import           Data.List.NonEmpty (NonEmpty)
import qualified Data.Set           as S

import Lambda.Core.AST.Binding
import qualified Lambda.Core.AST.Definitions    as C
import qualified Lambda.Core.AST.Expr    as C
import Lambda.Core.AST.Identifier
import Lambda.Core.AST.Literal
import Lambda.Core.AST.Types
import Lambda.Core.AST.Pattern

data SyntaxError = MalformedHead Type
  deriving (Eq, Show)

makeClassyPrisms ''SyntaxError

-- | Naive generalization that closes over every free variable
generalize :: S.Set Type -> Type -> TypeScheme
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

desugar :: (AsSyntaxError e, MonadError e m) => Definition -> m C.Definition
desugar (Data name typeArgs constructors) = pure $ C.Data name typeArgs constructors
desugar (TypeSignature name ty) = pure $ C.TypeSignature name ty
desugar (Function def) = pure . C.Function $ translateDefinition def
desugar (Class constraints classType classMembers) = do
  (className, tyVars) <- asClassDef classType
  pure $ C.Class constraints className tyVars classMembers
desugar (Instance constraints classType classImpls) = do
  (className, tyArgs) <- asClassInstance classType
  unless (all (sameConstructor className) constraints) . throwError $ _MalformedHead # classType
  pure . C.Instance constraints className tyArgs $ fmap translateDefinition classImpls
  where
    sameConstructor name (TyApp (TyCon (TypeCon name')) _) = name == name'
    sameConstructor _ _ = False

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
  = Data Identifier [Identifier] (NonEmpty C.ProdDecl)
  | TypeSignature Identifier TypeScheme
  | Function FunctionDefinition
  | Class (S.Set Type) Type [(Identifier, Type)]
  | Instance (S.Set Type) Type [FunctionDefinition]

data Expr
  = Id Identifier
  | Lit Literal
  | Prod Identifier [Expr]
  | App Expr Expr
  | Abs Identifier Expr
  | Let FunctionDefinition Expr
  | Rec FunctionDefinition Expr
  | Case Expr (NonEmpty (Pattern,Expr))
  | Error String

data FunctionDefinition = FunctionDefinition Identifier [Identifier] Expr

translateDefinition :: FunctionDefinition -> Binding C.Expr
translateDefinition (FunctionDefinition name args expr) = Binding name $ foldr C.Abs (desugarExpr expr) args
