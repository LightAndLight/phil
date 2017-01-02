{-# language FlexibleContexts #-}

module Lambda.Core.Codegen (genPHP) where

import           Control.Monad.State
import Data.Foldable (traverse_)
import Data.Maybe
import           Data.DList

import           Lambda.Core.AST
import           Lambda.PHP.AST

genPHP :: [Definition] -> PHP
genPHP defs = PHP . toList $ execState (traverse_ genPHPDecl defs) empty

toFunction :: Expr -> Maybe (Expr, [Identifier])
toFunction (Abs varName expr) = Just $ (varName :) <$> go expr
  where
    go (Abs varName' expr') = (varName' :) <$> go expr'
    go expr' = (expr',[])
toFunction _ = Nothing

genFunctionBody :: Expr -> [PHPStatement]
genFunctionBody expr
  = let (ret,statements) = runState (genPHPExpr expr) empty
    in toList $ statements `snoc` PHPStatementReturn ret

genPHPDecl :: MonadState (DList PHPDecl) m => Definition -> m ()
genPHPDecl (Data name _ constructors) = undefined
genPHPDecl (Binding name value)
  = let functionDetails = toFunction value
    in case functionDetails of
      Nothing -> do
        let (assign,decls) = runState (genPHPAssignment name value) empty
        modify $ flip append (fmap PHPDeclStatement $ decls `snoc` assign)
      Just (body,args) ->
        modify . flip snoc $ PHPDeclFunc (phpId name) (fmap phpId args) (genFunctionBody body)

genPHPLiteral :: Literal -> PHPLiteral
genPHPLiteral (LitInt i) = PHPInt i
genPHPLiteral (LitString s) = PHPString s
genPHPLiteral (LitChar c) = PHPString [c]

genPHPExpr :: MonadState (DList PHPStatement) m => Expr -> m PHPExpr
genPHPExpr (Id name) = pure . PHPExprVar $ phpId name
genPHPExpr (Lit lit) = pure . PHPExprLiteral $ genPHPLiteral lit
genPHPExpr (Prod name args) = undefined
genPHPExpr (App f x) = PHPExprFunctionCall <$> genPHPExpr f <*> (pure <$> genPHPExpr x)
genPHPExpr f@(Abs name _)
  = let (body,args) = fromJust $ toFunction f
    in PHPExprFunction (fmap phpId args) <$> (pure . PHPStatementReturn <$> genPHPExpr body)
genPHPExpr (Let var value rest) = do
  assign <- genPHPAssignment var value
  modify $ flip snoc assign
  genPHPExpr rest
genPHPExpr (Case val branches) = undefined
genPHPExpr (Error str) = pure $ PHPExprFunctionCall (PHPExprFunction [] [PHPStatementThrow $ PHPExprNew $ phpId "Exception"]) []

genPHPAssignment :: MonadState (DList PHPStatement) m => Identifier -> Expr -> m PHPStatement
genPHPAssignment name value = PHPStatementExpr . PHPExprAssign (phpId name) <$> genPHPExpr value
