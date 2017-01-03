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

genConstructor :: ProdDecl -> [PHPDecl]
genConstructor (ProdDecl name args) = [classDecl, funcDecl]
  where
    className = phpId name
    argNames = take (length args) $ fmap (phpId . (++) "a" . show) [1..]
    classDecl
      = PHPDeclClass className
        [ PHPClassFunc False Public (phpId "__construct") argNames
          [ PHPStatementExpr $ PHPExprAssign (PHPExprClassAccess (PHPExprVar $ phpId "this") (phpId "values") Nothing) (PHPExprLiteral . PHPArray $ fmap PHPExprVar argNames)]
        ]
    funcDecl = case argNames of
      [] -> PHPDeclFunc className [] [PHPStatementReturn $ PHPExprNew className []]
      arg:rest -> PHPDeclFunc className [arg] [PHPStatementReturn $ runReader (go rest) [arg]]
      where
        go :: MonadReader [PHPId] m => [PHPId] -> m PHPExpr
        go [] = pure . PHPExprNew className $ fmap PHPExprVar argNames
        go (arg:rest) = do
          res <- local (arg :) $ go rest
          scope <- ask
          pure $ PHPExprFunction [arg] (Just scope) [PHPStatementReturn res]

genPHPDecl :: MonadState (DList PHPDecl) m => Definition -> m ()
genPHPDecl (Data _ _ constructors) = do
  let decls = genConstructor =<< N.toList constructors
  modify $ flip append (fromList decls)
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
      pure [PHPStatementExpr $ PHPExprAssign (PHPExprVar name') val, PHPStatementReturn res']
    genBranch val (PatLit lit,res) = do
      res' <- genPHPExpr res
      pure [PHPStatementIfThenElse (PHPExprBinop Equal val (PHPExprLiteral $ genPHPLiteral lit)) [PHPStatementReturn res'] Nothing]
    genBranch val (PatCon name args,res) = do
      let assignments = genBinding <$> zip [0..] args
      res' <- local (fmap phpId args ++) $ genPHPExpr res
      pure [PHPStatementIfThenElse (PHPExprBinop InstanceOf val (PHPExprName $ phpId name)) (assignments ++ [PHPStatementReturn res']) Nothing]
      where
        genBinding (ix,arg)
          = PHPStatementExpr $
              PHPExprAssign
                (PHPExprVar $ phpId arg)
                (PHPExprArrayAccess
                  (PHPExprClassAccess val (phpId "values") Nothing)
                  (PHPExprLiteral $ PHPInt ix))
genPHPExpr (Error str) = pure $ PHPExprFunctionCall (PHPExprFunction [] Nothing [PHPStatementThrow $ PHPExprNew (phpId "Exception") []]) []

genPHPAssignment :: MonadReader [PHPId] m => Identifier -> Expr -> m PHPStatement
genPHPAssignment name value = PHPStatementExpr . PHPExprAssign (PHPExprVar $ phpId name) <$> genPHPExpr value
