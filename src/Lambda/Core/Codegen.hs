{-# language FlexibleContexts #-}
{-# language TemplateHaskell #-}

module Lambda.Core.Codegen (genPHP) where

import Control.Lens
import Control.Monad.Reader
import           Control.Monad.State
import Data.Foldable (traverse_)
import qualified Data.List.NonEmpty as N
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe
import Data.DList (DList)
import           qualified Data.DList as D

import           Lambda.Core.AST
import Lambda.Core.Typecheck
import           Lambda.PHP.AST

data CodegenEnv
  = CodegenEnv
  { _codegenContext :: Map Identifier TypeScheme
  , _codegenScope :: [PHPId]
}

makeClassy ''CodegenEnv

class HasScope s where
  scope :: Lens' s [PHPId]

instance HasScope CodegenEnv where
  scope = codegenEnv . codegenScope

instance HasContext CodegenEnv where
  context = codegenEnv . codegenContext

genPHP :: Map Identifier TypeScheme -> [Definition] -> PHP
genPHP ctxt defs = PHP . D.toList $ runReader (execStateT (traverse_ genPHPDecl defs) D.empty) (CodegenEnv ctxt [])

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

genPHPDecl :: (HasContext r, MonadReader r m, MonadState (DList PHPDecl) m) => Definition -> m ()
genPHPDecl (Data _ _ constructors) = do
  let decls = genConstructor =<< N.toList constructors
  modify $ flip D.append (D.fromList decls)
genPHPDecl (Binding name value)
  = let functionDetails = toFunction value
    in do
      ctxt <- view context
      case functionDetails of
        Nothing -> modify . flip D.snoc . PHPDeclStatement $ runReader (genPHPAssignment name value) (CodegenEnv ctxt [])
        Just (body,arg) -> do
          let arg' = phpId arg
          modify . flip D.snoc $ PHPDeclFunc (phpId name) [arg'] [PHPStatementReturn $ runReader (genPHPExpr body) (CodegenEnv ctxt [arg'])]

genPHPLiteral :: Literal -> PHPLiteral
genPHPLiteral (LitInt i) = PHPInt i
genPHPLiteral (LitString s) = PHPString s
genPHPLiteral (LitChar c) = PHPString [c]

genPHPExpr :: (HasContext r, HasScope r, MonadReader r m) => Expr -> m PHPExpr
genPHPExpr (Id name) = do
  maybeTy <- views context (M.lookup name)
  pure $ case maybeTy of
    Just ty -> case baseType ty of
      FunType{} -> PHPExprName $ phpId name
      _ -> PHPExprVar $ phpId name
    Nothing -> PHPExprVar $ phpId name
  where
    baseType (Base ty) = ty
    baseType (Forall _ ty) = baseType ty
genPHPExpr (Lit lit) = pure . PHPExprLiteral $ genPHPLiteral lit
genPHPExpr (Prod name args)
  = foldr f (pure $ PHPExprFunctionCall (PHPExprName $ phpId name) []) args
  where
    f arg call = PHPExprFunctionCall <$> call <*> (pure <$> genPHPExpr arg)
genPHPExpr (App f x) = do
  f' <- genPHPExpr f
  x' <- genPHPExpr x
  pure $ PHPExprFunctionCall f' [x']
genPHPExpr (Abs name body) = do
  sc <- view scope
  let name' = phpId name
  body' <- local (over scope (name' :)) $ genPHPExpr body
  pure $ PHPExprFunction [name'] (Just sc) [PHPStatementReturn body']
genPHPExpr (Let var value rest) = do
  assignment <- genPHPAssignment var value
  rest' <- local (over scope (phpId var :)) $ genPHPExpr rest
  sc <- view scope
  pure $ PHPExprFunctionCall (PHPExprFunction [] (Just sc) [assignment, PHPStatementReturn rest']) []
genPHPExpr (Case val branches) = do
  val' <- genPHPExpr val
  branches' <- join . N.toList <$> traverse (genBranch val') branches
  sc <- view scope
  pure $ PHPExprFunctionCall (PHPExprFunction [] (Just sc) branches') []
  where
    genBranch :: (HasScope r, HasContext r, MonadReader r m) => PHPExpr -> (Pattern,Expr) -> m [PHPStatement]
    genBranch val (PatId name,res) = do
      let name' = phpId name
      res' <- local (over scope (name' :)) $ genPHPExpr res
      pure [PHPStatementExpr $ PHPExprAssign (PHPExprVar name') val, PHPStatementReturn res']
    genBranch val (PatLit lit,res) = do
      res' <- genPHPExpr res
      pure [PHPStatementIfThenElse (PHPExprBinop Equal val (PHPExprLiteral $ genPHPLiteral lit)) [PHPStatementReturn res'] Nothing]
    genBranch val (PatCon name args,res) = do
      let assignments = genBinding <$> zip [0..] args
      res' <- local (over scope (fmap phpId args ++)) $ genPHPExpr res
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

genPHPAssignment :: (HasScope r, HasContext r, MonadReader r m) => Identifier -> Expr -> m PHPStatement
genPHPAssignment name value = PHPStatementExpr . PHPExprAssign (PHPExprVar $ phpId name) <$> genPHPExpr value
