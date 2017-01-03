{-# language FlexibleContexts #-}

module Lambda.Core.Codegen (genPHP) where

import Control.Monad.Reader
import           Control.Monad.State
import Data.Foldable (traverse_)
import qualified Data.List.NonEmpty as N
import Data.Maybe
import           Data.DList

import           Lambda.Core.AST
import           Lambda.PHP.AST

genPHP :: [Definition] -> PHP
genPHP defs = PHP . toList $ execState (traverse_ genPHPDecl defs) empty

toFunction :: Expr -> Maybe (Expr, Identifier)
toFunction (Abs varName expr) = Just (expr,varName)
toFunction _ = Nothing

genPHPDecl :: MonadState (DList PHPDecl) m => Definition -> m ()
genPHPDecl (Data name _ constructors) = undefined
genPHPDecl (Binding name value)
  = let functionDetails = toFunction value
    in case functionDetails of
      Nothing -> modify . flip snoc . PHPDeclStatement $ runReader (genPHPAssignment name value) []
      Just (body,arg) -> do
        let arg' = phpId arg
        modify . flip snoc $ PHPDeclFunc (phpId name) [arg'] [PHPStatementReturn $ runReader (genPHPExpr body) [arg']]

genPHPLiteral :: Literal -> PHPLiteral
genPHPLiteral (LitInt i) = PHPInt i
genPHPLiteral (LitString s) = PHPString s
genPHPLiteral (LitChar c) = PHPString [c]

genPHPExpr :: MonadReader [PHPId] m => Expr -> m PHPExpr
genPHPExpr (Id name) = pure . PHPExprVar $ phpId name
genPHPExpr (Lit lit) = pure . PHPExprLiteral $ genPHPLiteral lit
genPHPExpr (Prod name args) = undefined
genPHPExpr (App f x) = do
  f' <- genPHPExpr f
  x' <- genPHPExpr x
  pure $ PHPExprFunctionCall f' [x']
genPHPExpr (Abs name body) = do
  scope <- ask
  let name' = phpId name
  body' <- local (name' :) $ genPHPExpr body
  pure $ PHPExprFunction [name'] (Just scope) [PHPStatementReturn body']
genPHPExpr (Let var value rest) = do
  assignment <- genPHPAssignment var value
  rest' <- local (phpId var :) $ genPHPExpr rest
  scope <- ask
  pure $ PHPExprFunctionCall (PHPExprFunction [] (Just scope) [assignment, PHPStatementReturn rest']) []
genPHPExpr (Case val branches) = do
  val' <- genPHPExpr val
  branches' <- join . N.toList <$> traverse (genBranch val') branches
  scope <- ask
  pure $ PHPExprFunctionCall (PHPExprFunction [] (Just scope) branches') []
  where
    genBranch :: MonadReader [PHPId] m => PHPExpr -> (Pattern,Expr) -> m [PHPStatement]
    genBranch val (PatId name,res) = do
      let name' = phpId name
      res' <- local (name' :) $ genPHPExpr res
      pure [PHPStatementExpr $ PHPExprAssign name' val, PHPStatementReturn res']
    genBranch val (PatCon a1 a2,res) = undefined
    genBranch val (PatLit lit,res) = do
      res' <- genPHPExpr res
      pure [PHPStatementIfThenElse (PHPExprBinop Equal val (PHPExprLiteral $ genPHPLiteral lit)) [PHPStatementReturn res'] Nothing]
genPHPExpr (Error str) = pure $ PHPExprFunctionCall (PHPExprFunction [] Nothing [PHPStatementThrow $ PHPExprNew $ phpId "Exception"]) []

genPHPAssignment :: MonadReader [PHPId] m => Identifier -> Expr -> m PHPStatement
genPHPAssignment name value = PHPStatementExpr . PHPExprAssign (phpId name) <$> genPHPExpr value
