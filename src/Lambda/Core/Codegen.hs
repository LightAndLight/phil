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
import Data.Set (Set)
import qualified Data.Set as S

import           Lambda.Core.AST
import Lambda.Core.Typecheck
import           Lambda.PHP.AST

data CodegenState
  = CodegenState
  { _codegenScope :: Set PHPId
  , _codegenCode :: DList PHPDecl
  }

makeClassy ''CodegenState

class HasScope s where
  scope :: Lens' s (Set PHPId)

class HasCode s where
  code :: Lens' s (DList PHPDecl)

instance HasScope CodegenState where
  scope = codegenState . codegenScope

instance HasCode CodegenState where
  code = codegenState . codegenCode

genPHP :: [Definition] -> PHP
genPHP defs
  = let finalState = execState (traverse_ genPHPDecl defs) (CodegenState S.empty D.empty)
    in PHP $ D.toList (finalState ^. code)

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
    func = case argNames of
      [] -> PHPExprNew className []
      _ -> runReader (go argNames) []
      where
        go :: MonadReader [PHPId] m => [PHPId] -> m PHPExpr
        go [] = pure . PHPExprNew className $ fmap PHPExprVar argNames
        go (arg:rest) = do
          res <- local (arg :) $ go rest
          scope <- ask
          pure $ PHPExprFunction [arg] scope [PHPStatementReturn res]
    funcDecl = PHPDeclStatement . PHPStatementExpr $ PHPExprAssign (PHPExprVar className) func

genPHPDecl :: (HasCode s, HasScope s, MonadState s m) => Definition -> m ()
genPHPDecl (Data _ _ constructors) = do
  let decls = genConstructor =<< N.toList constructors
  code %= flip D.append (D.fromList decls)
genPHPDecl (Binding name value) = do
  scope .= S.empty
  assignment <- genPHPAssignment name value
  code %= flip D.snoc (PHPDeclStatement assignment)

genPHPLiteral :: Literal -> PHPLiteral
genPHPLiteral (LitInt i) = PHPInt i
genPHPLiteral (LitString s) = PHPString s
genPHPLiteral (LitChar c) = PHPString [c]
genPHPLiteral (LitBool b) = PHPBool b

genPHPExpr :: (HasScope s, MonadState s m) => Expr -> m PHPExpr
genPHPExpr (Id name) = do
  let name' = phpId name
  scope %= S.insert name'
  pure $ PHPExprVar name'
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
  let name' = phpId name
  body' <- genPHPExpr body
  scope %= S.delete name'
  sc <- use scope
  pure $ PHPExprFunction [name'] (S.toList sc) [PHPStatementReturn body']
genPHPExpr (Let var value rest) = do
  assignment <- genPHPAssignment var value
  rest' <- genPHPExpr rest
  scope %= S.delete (phpId var)
  sc <- use scope
  pure $ PHPExprFunctionCall (PHPExprFunction [] (S.toList sc) [assignment, PHPStatementReturn rest']) []
genPHPExpr (Case val branches) = do
  val' <- genPHPExpr val
  branches' <- join . N.toList <$> traverse (genBranch val') branches
  sc <- use scope
  pure $ PHPExprFunctionCall (PHPExprFunction [] (S.toList sc) branches') []
  where
    genBranch :: (HasScope s, MonadState s m) => PHPExpr -> (Pattern,Expr) -> m [PHPStatement]
    genBranch val (PatId name,res) = do
      let name' = phpId name
      res' <- genPHPExpr res
      scope %= S.delete name'
      pure [PHPStatementExpr $ PHPExprAssign (PHPExprVar name') val, PHPStatementReturn res']
    genBranch val (PatLit lit,res) = do
      res' <- genPHPExpr res
      pure [PHPStatementIfThenElse (PHPExprBinop Equal val (PHPExprLiteral $ genPHPLiteral lit)) [PHPStatementReturn res'] Nothing]
    genBranch val (PatCon name args,res) = do
      let args' = fmap phpId args
      sc <- use scope
      let localArgs = filter (not . flip S.member sc) args'
      let assignments = genBinding <$> zip [0..] args'
      res' <- genPHPExpr res
      scope %= flip (foldr S.delete) localArgs
      pure [PHPStatementIfThenElse (PHPExprBinop InstanceOf val (PHPExprName $ phpId name)) (assignments ++ [PHPStatementReturn res']) Nothing]
      where
        genBinding (ix,arg)
          = PHPStatementExpr $
              PHPExprAssign
                (PHPExprVar arg)
                (PHPExprArrayAccess
                  (PHPExprClassAccess val (phpId "values") Nothing)
                  (PHPExprLiteral $ PHPInt ix))
genPHPExpr (Error str) = pure $ PHPExprFunctionCall (PHPExprFunction [] [] [PHPStatementThrow $ PHPExprNew (phpId "Exception") []]) []

genPHPAssignment :: (HasScope s, MonadState s m) => Identifier -> Expr -> m PHPStatement
genPHPAssignment name value = PHPStatementExpr . PHPExprAssign (PHPExprVar $ phpId name) <$> genPHPExpr value
