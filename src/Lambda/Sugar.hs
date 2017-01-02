module Lambda.Sugar(Definition(..), Expr(..), FunctionDefinition(..), desugar, desugarExpr) where

import           Data.List.NonEmpty (NonEmpty)

import qualified Lambda.Core.AST    as C

desugar :: Definition -> C.Definition
desugar (Data name typeArgs constructors) = C.Data name typeArgs constructors
desugar (Function def) = translateDefinition def

desugarExpr :: Expr -> C.Expr
desugarExpr (Id n) = C.Id n
desugarExpr (Lit l) = C.Lit l
desugarExpr (Prod name args) = C.Prod name (fmap desugarExpr args)
desugarExpr (App f x) = C.App (desugarExpr f) (desugarExpr x)
desugarExpr (Abs n expr) = C.Abs n $ desugarExpr expr
desugarExpr (Let def expr)
  = let C.Binding name value = translateDefinition def
    in C.Let name value $ desugarExpr expr
desugarExpr (Case n bs) = C.Case (desugarExpr n) $ fmap (fmap desugarExpr) bs
desugarExpr (Error err) = C.Error err

data Definition
  = Data C.Identifier [C.Identifier] (NonEmpty C.ProdDecl)
  | Function FunctionDefinition

data Expr
  = Id C.Identifier
  | Lit C.Literal
  | Prod C.Identifier [Expr]
  | App Expr Expr
  | Abs C.Identifier Expr
  | Let FunctionDefinition Expr
  | Case Expr (NonEmpty (C.Pattern,Expr))
  | Error String

data FunctionDefinition = FunctionDefinition C.Identifier [C.Identifier] Expr

translateDefinition :: FunctionDefinition -> C.Definition
translateDefinition (FunctionDefinition name args expr) = C.Binding name $ foldr C.Abs (desugarExpr expr) args
