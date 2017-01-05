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

data ArgType = Reference | Value

data CodegenState
  = CodegenState
  { _codegenScope :: Map PHPId ArgType
  , _codegenCode :: DList PHPDecl
  }

makeClassy ''CodegenState

class HasScope s where
  scope :: Lens' s (Map PHPId ArgType)

class HasCode s where
  code :: Lens' s (DList PHPDecl)

instance HasScope CodegenState where
  scope = codegenState . codegenScope

instance HasCode CodegenState where
  code = codegenState . codegenCode

genPHP :: [Definition] -> PHP
genPHP defs
  = let finalState = execState (traverse_ genPHPDecl defs) (CodegenState M.empty D.empty)
    in PHP $ D.toList (finalState ^. code)

toFunction :: Expr -> Maybe (Expr, Identifier)
toFunction (Abs varName expr) = Just (expr,varName)
toFunction _ = Nothing

scopeToArgs :: Map PHPId ArgType -> [PHPArg]
scopeToArgs = M.foldrWithKey (\k a -> (valueOrReference k a :)) []
  where
    valueOrReference name argType = case argType of
      Value -> PHPArgValue name
      Reference -> PHPArgReference name

genConstructor :: ProdDecl -> [PHPDecl]
genConstructor (ProdDecl name args) = [classDecl, funcDecl]
  where
    argNames = take (length args) $ fmap (phpId . (++) "a" . show) [1..]
    className = phpId $ name ++ "Con"
    classDecl
      = PHPDeclClass className
        [ PHPClassFunc False Public (phpId "__construct") (fmap PHPArgValue argNames)
          [ PHPStatementExpr $ PHPExprAssign (PHPExprClassAccess (PHPExprVar $ phpId "this") (phpId "values") Nothing) (PHPExprLiteral . PHPArray $ fmap PHPExprVar argNames)]
        ]
    func = case fmap PHPArgValue argNames of
      [] -> PHPExprNew className []
      argNames' -> runReader (go argNames') []
      where
        go :: MonadReader [PHPArg] m => [PHPArg] -> m PHPExpr
        go [] = pure . PHPExprNew className $ fmap PHPExprVar argNames
        go (arg:rest) = do
          res <- local (arg :) $ go rest
          scope <- ask
          pure $ PHPExprFunction [arg] scope [PHPStatementReturn res]
    funcDecl = PHPDeclStatement . PHPStatementExpr $ PHPExprAssign (PHPExprVar $ phpId name) func

genPHPDecl :: (HasCode s, HasScope s, MonadState s m) => Definition -> m ()
genPHPDecl (Data _ _ constructors) = do
  let decls = genConstructor =<< N.toList constructors
  code %= flip D.append (D.fromList decls)
genPHPDecl (Function binding) = do
  scope .= M.empty
  assignment <- genPHPAssignment binding
  code %= flip D.snoc (PHPDeclStatement assignment)

genPHPLiteral :: Literal -> PHPLiteral
genPHPLiteral (LitInt i) = PHPInt i
genPHPLiteral (LitString s) = PHPString s
genPHPLiteral (LitChar c) = PHPString [c]
genPHPLiteral (LitBool b) = PHPBool b

genPHPExpr :: (HasScope s, MonadState s m) => Expr -> m PHPExpr
genPHPExpr (Id name) = do
  let name' = phpId name
  scope %= M.insertWith (flip const) name' Value
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
  scope %= M.delete name'
  sc <- use scope
  pure $ PHPExprFunction [PHPArgValue name'] (scopeToArgs sc) [PHPStatementReturn body']
genPHPExpr (Let binding rest) = do
  assignment <- genPHPAssignment binding
  rest' <- genPHPExpr rest
  scope %= M.delete (phpId $ bindingName binding)
  sc <- use scope
  pure $ PHPExprFunctionCall (PHPExprFunction [] (scopeToArgs sc) [assignment, PHPStatementReturn rest']) []
genPHPExpr (Rec binding rest) = do
  let name = phpId $ bindingName binding
  scope %= M.insert name Reference
  assignment <- genPHPAssignment binding
  rest' <- genPHPExpr rest
  scope %= M.delete name
  sc <- use scope
  pure $ PHPExprFunctionCall (PHPExprFunction [] (scopeToArgs sc) [assignment, PHPStatementReturn rest']) []
genPHPExpr (Case val branches) = do
  val' <- genPHPExpr val
  branches' <- join . N.toList <$> traverse (genBranch val') branches
  sc <- use scope
  pure $ PHPExprFunctionCall (PHPExprFunction [] (scopeToArgs sc) branches') []
  where
    genBranch :: (HasScope s, MonadState s m) => PHPExpr -> (Pattern,Expr) -> m [PHPStatement]
    genBranch val (PatWildcard,res) = do
      res' <- genPHPExpr res
      pure [PHPStatementReturn res']
    genBranch val (PatId name,res) = do
      let name' = phpId name
      res' <- genPHPExpr res
      scope %= M.delete name'
      pure [PHPStatementExpr $ PHPExprAssign (PHPExprVar name') val, PHPStatementReturn res']
    genBranch val (PatLit lit,res) = do
      res' <- genPHPExpr res
      pure [PHPStatementIfThenElse (PHPExprBinop Equal val (PHPExprLiteral $ genPHPLiteral lit)) [PHPStatementReturn res'] Nothing]
    genBranch val (PatCon name args,res) = do
      let args' = fmap phpId args
      sc <- use scope
      let localArgs = filter (not . flip M.member sc) args'
      let assignments = genBinding <$> zip [0..] args'
      res' <- genPHPExpr res
      scope %= flip (foldr M.delete) localArgs
      pure [PHPStatementIfThenElse (PHPExprBinop InstanceOf val (PHPExprName . phpId $ name ++ "Con")) (assignments ++ [PHPStatementReturn res']) Nothing]
      where
        genBinding (ix,arg)
          = PHPStatementExpr $
              PHPExprAssign
                (PHPExprVar arg)
                (PHPExprArrayAccess
                  (PHPExprClassAccess val (phpId "values") Nothing)
                  (PHPExprLiteral $ PHPInt ix))
genPHPExpr (Error str) = pure $ PHPExprFunctionCall (PHPExprFunction [] [] [PHPStatementThrow $ PHPExprNew (phpId "Exception") []]) []

genPHPAssignment :: (HasScope s, MonadState s m) => Binding -> m PHPStatement
genPHPAssignment (Binding name value) = PHPStatementExpr . PHPExprAssign (PHPExprVar $ phpId name) <$> genPHPExpr value
