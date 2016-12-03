{-# language FlexibleContexts #-}

module Lambda.Translation (exprToCore, toCore) where

import Control.Applicative
import Control.Monad.Reader
import Data.Maybe
import Data.List
import Data.Set (Set)
import qualified Data.Set as S

import qualified Lambda.AST  as A
import qualified Lambda.Core as C

newVar :: MonadReader (Set C.Identifier) m => m C.Identifier
newVar = do
  frees <- ask
  return . fromJust . find (not . flip S.member frees) $ fmap (\n -> "a" ++ show n) [1..]

translateExpr :: MonadReader (Set C.Identifier) m => A.Expr -> m C.Expr
translateExpr (A.Id name) = return $ C.Id name
translateExpr (A.Lit lit) = return $ C.Lit lit
translateExpr (A.Prod name vals) = C.Prod name <$> traverse translateExpr vals
translateExpr (A.App f x) = C.App <$> translateExpr f <*> translateExpr x
translateExpr (A.Abs name body)
  = local (S.insert name) (C.Abs name <$> translateExpr body)
translateExpr (A.Let name val rest)
  = local (S.insert name) (C.Let name <$> translateExpr val <*> translateExpr rest)
translateExpr (A.Case cond branches) = do
  free <- ask
  var <- newVar
  branches' <- traverse (local (S.insert var) . uncurry toLambdaSingle) branches
  return . C.Abs var $ foldr C.Chain (C.Error "Inexhaustive pattern match") branches'

toLambdaWith :: MonadReader (Set C.Identifier) m => A.Pattern -> A.Expr -> (A.Expr -> m C.Expr) -> m C.Expr
toLambdaWith (A.PatCon conName args) expr f
  = C.PatAbs (C.PatCon conName args) <$> local (S.fromList args `S.union`) (f expr)
toLambdaWith (A.PatId name) expr f = C.Abs name <$> local (S.insert name) (f expr)
toLambdaWith (A.PatLit lit) expr f = C.PatAbs (C.PatLit lit) <$> f expr

toLambdaSingle :: MonadReader (Set C.Identifier) m => A.Pattern -> A.Expr -> m C.Expr
toLambdaSingle pat expr = toLambdaWith pat expr translateExpr

toLambdaMulti :: MonadReader (Set C.Identifier) m => [A.Pattern] -> A.Expr -> m C.Expr
toLambdaMulti [] expr = translateExpr expr
toLambdaMulti (p:ps) expr = toLambdaWith p expr (toLambdaMulti ps)

toCore :: [A.Definition] -> [C.Definition]
toCore = flip runReader S.empty . traverse translateDefinition
  where
    translateDefinition :: MonadReader (Set C.Identifier) m => A.Definition -> m C.Definition
    translateDefinition (A.Data name args prods) = return $ C.Data name args prods
    translateDefinition (A.Function name args body) = C.Binding name <$> toLambdaMulti args body

exprToCore :: A.Expr -> C.Expr
exprToCore = flip runReader S.empty . translateExpr
