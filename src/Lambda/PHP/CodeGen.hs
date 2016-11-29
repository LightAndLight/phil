module Lambda.PHP.CodeGen where

import           Data.Foldable
import           Data.List.NonEmpty (NonEmpty (..))
import           Data.Monoid

import           Lambda
import           Lambda.PHP.AST

toPHP :: [Definition] -> PHP
toPHP defs = PHP $ foldMap toPHPDecl defs

toArgs :: [a] -> [PHPId]
toArgs args = take (length args) $ fmap (\n -> PHPId $ "arg" ++ show n) [0..]

toPHPDecl :: Definition -> [PHPDecl]
toPHPDecl (Data (DataDecl name _ cons))
  = toList $ fmap (toPHPDecl' name) cons
  where
    toPHPDecl' :: String -> ProdDecl -> PHPDecl
    toPHPDecl' typeName (ProdDecl conName args)
      = let args' = toArgs args in
        PHPDeclClass
          (PHPId $ typeName <> "_" <> conName)
          [ PHPClassVar False Public (PHPId "tag") Nothing
          , PHPClassFunc False Public (PHPId "__construct") args' $
              PHPStatementExpr
                (PHPExprAssign (PHPExprClassAccess (PHPExprVar $ PHPId "this") (PHPId "tag") Nothing) (PHPExprLiteral $ PHPString conName))
              : fmap (\a -> PHPStatementExpr (PHPExprAssign (PHPExprClassAccess (PHPExprVar $ PHPId "this") a Nothing) (PHPExprVar a))) args'
          ]
toPHPDecl (Binding name expr) = _
