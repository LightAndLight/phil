module Lambda.Core.AST.Expr where

import Data.Bifunctor
import           Data.List.NonEmpty         (NonEmpty)
import           Data.Map                   (Map)
import           Data.Set                   (Set)
import           qualified Data.Set                   as S

import           Lambda.Core.AST.Binding
import           Lambda.Core.AST.Evidence
import           Lambda.Core.AST.Identifier
import           Lambda.Core.AST.Literal
import           Lambda.Core.AST.Pattern
import           Lambda.Core.AST.Types

data Expr
  = Id Identifier
  | Lit Literal
  | Prod Identifier [Expr]
  | App Expr Expr
  | Abs Identifier Expr
  | DictAbs EVar Expr
  | DictApp Expr Dictionary
  | DictSel Identifier Dictionary
  | Let (Binding Expr) Expr
  | Rec (Binding Expr) Expr
  | Case Expr (NonEmpty (Pattern,Expr))
  | Error String
  deriving (Eq, Show)

exprEVars :: Expr -> Set EVar
exprEVars (Prod _ a2) = foldMap exprEVars a2
exprEVars (App a1 a2) = exprEVars a1 `S.union` exprEVars a2
exprEVars (Abs _ a2) = exprEVars a2
exprEVars (DictAbs var a2) = exprEVars a2 `S.difference` S.singleton var
exprEVars (DictApp a1 a2) = exprEVars a1 `S.union` dictEVars a2
exprEVars (DictSel _ a2) = dictEVars a2
exprEVars (Let a1 a2) = exprEVars a2
exprEVars (Rec a1 a2) = exprEVars a2
exprEVars (Case a1 a2) = exprEVars a1 `S.union` foldMap (exprEVars . snd) a2
exprEVars _ = S.empty

replaceDicts :: EVar -> Dictionary -> Expr -> Expr
replaceDicts eVar dict expr = case expr of
  Prod cons exprs -> Prod cons $ fmap (replaceDicts eVar dict) exprs
  App f x -> App (replaceDicts eVar dict f) (replaceDicts eVar dict x)
  Abs name body -> Abs name (replaceDicts eVar dict body)
  DictAbs eVar' body
    | eVar /= eVar' -> DictAbs eVar' (replaceDicts eVar dict body)
    | otherwise -> expr
  DictApp expr' evidence -> DictApp (replaceDicts eVar dict expr') $ subDict (eVar, dict) evidence
  DictSel name evidence -> DictSel name $ subDict (eVar, dict) evidence
  Let (Binding name value) rest -> Let (Binding name $ replaceDicts eVar dict value) (replaceDicts eVar dict rest)
  Rec (Binding name value) rest -> Rec (Binding name $ replaceDicts eVar dict value) (replaceDicts eVar dict rest)
  Case input branches -> Case (replaceDicts eVar dict input) $ fmap (second $ replaceDicts eVar dict) branches
  _ -> expr
