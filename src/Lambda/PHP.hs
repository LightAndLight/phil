{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell            #-}

module Lambda.PHP (toSource) where

import           Control.Lens        (makeLenses, use, (%=), (+=), (-=))
import           Control.Monad.State
import           Data.DList          (DList, cons)
import           Data.Foldable
import           Data.List           (intercalate)
import           Data.Monoid

import           Lambda.PHP.AST

data SourceState = SourceState { _indentSequence :: String, _indentLevel :: Int, _output :: DList String }
makeLenses ''SourceState

newtype SourceM a = SourceM { unSourceM :: State SourceState a }
  deriving (Functor, Applicative, Monad, MonadState SourceState)

indent :: SourceM ()
indent = indentLevel += 1

dedent :: SourceM ()
dedent = do
  level <- use indentLevel
  when (level > 0) (indentLevel -= 1)

line :: String -> SourceM ()
line input = do
  level <- use indentLevel
  indentSeq <- use indentSequence
  output %= cons (join (replicate level indentSeq) <> input <> "\n")

manyLines :: [String] -> SourceM ()
manyLines = traverse_ line

indented :: SourceM a -> SourceM ()
indented body = do
  indent
  body
  dedent

phpToSource :: PHP -> SourceM ()
phpToSource (PHP decls) = do
  line "<?php"
  line ""
  traverse phpDeclToSource decls
  line ""
  line "?>"

phpDeclToSource :: PHPDecl -> SourceM ()
phpDeclToSource (PHPDeclFunc name args body) = do
  line $ "function " <> unPHPId name <> " (" <> intercalate ", " (fmap unPHPId args) <> ") {"
  indented $ traverse phpStatementToSource body
  line "}"
phpDeclToSource (PHPDeclClass name members) = do
  line $ "class " <> unPHPId name <> " {"
  indented $ traverse phpClassMemberToSource members
  line "}"
phpDeclToSource (PHPDeclExpr expr) = do
  line ""
  phpExprToSource expr
  line ""

phpExprToSource :: PHPExpr -> SourceM ()
phpExprToSource e = _

phpClassMemberToSource :: PHPClassMember -> SourceM ()
phpClassMemberToSource m = _

phpStatementToSource :: PHPStatement -> SourceM ()
phpStatementToSource m = _
