module Lambda.Desugar.Decl where

import Data.List.NonEmpty

import           Lambda

data Decl
  = DeclData DataDecl
  | DeclFunc Identifier [Pattern] Expr

desugarDecls :: [Decl] -> [Definition]
desugarDecls [] = []
desugarDecls ((DeclData d):ds) = Data d : desugarDecls ds
desugarDecls (d@(DeclFunc name args body):ds)
  = let (group,rest) = span (sameName name) ds
    in Binding name $ toLambda args body
  where
    toCase (f :| fs)
    toLambda [] e = e
    toLambda (a:as) e = Abs a $ toLambda as e
