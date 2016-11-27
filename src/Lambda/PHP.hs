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

functionArgsToSource :: [PHPId] -> String
functionArgsToSource = intercalate ", " . fmap unPHPId

phpDeclToSource :: PHPDecl -> SourceM ()
phpDeclToSource (PHPDeclFunc name args body) = do
  line $ "function " <> unPHPId name <> " (" <> functionArgsToSource args <> ") {"
  indented $ traverse phpStatementToSource body
  line "}"
phpDeclToSource (PHPDeclClass name members) = do
  line $ "class " <> unPHPId name <> " {"
  indented $ traverse phpClassMemberToSource members
  line "}"
phpDeclToSource (PHPDeclExpr expr) = do
  line ""
  line $ phpExprToSource expr
  line ""
phpDeclToSource (PHPDeclStatement st) = do
  line ""
  phpStatementToSource st
  line ""

bracketed :: String -> String
bracketed input = "(" <> input <> ")"

phpExprToSource :: PHPExpr -> String
phpExprToSource (PHPExprVar name) = unPHPId name
phpExprToSource (PHPExprNew className) = "new " <> unPHPId className
phpExprToSource (PHPExprLiteral lit) = phpLiteralToSource lit
phpExprToSource (PHPExprBinop op left right)
  = unwords
      [ bracketed $ phpExprToSource left
      , binOpToSource op
      , bracketed $ phpExprToSource right
      ]
phpExprToSource (PHPExprUnop op arg) = unOpToSource op <> bracketed (phpExprToSource arg)
phpExprToSource (PHPExprAssign name expr)
  = unwords
      [ unPHPId name
      , phpExprToSource expr
      ]

visibilityToSource :: Visibility -> String
visibilityToSource Public = "public"
visibilityToSource Private = "private"
visibilityToSource Protected = "protected"

classMemberPrefix :: Bool -> Visibility -> [String]
classMemberPrefix True visibility = [visibilityToSource visibility, "static"]
classMemberPrefix False visibility = [visibilityToSource visibility]

phpClassMemberToSource :: PHPClassMember -> SourceM ()
phpClassMemberToSource (PHPClassFunc static visibility name args body) = do
  line . unwords $ classMemberPrefix static visibility <> ["function", unPHPId name <> "(" <> functionArgsToSource args <> ") {"]
  indented $ traverse phpStatementToSource body
  line "}"
phpClassMemberToSource (PHPClassVar static visibility name value)
  = line . unwords $ classMemberPrefix static visibility <> [unPHPId name] <> maybe [] (\e -> ["=", phpExprToSource e]) value

phpStatementToSource :: PHPStatement -> SourceM ()
phpStatementToSource m = _

phpLiteralToSource :: PHPLiteral -> String
phpLiteralToSource l = _

unOpToSource :: UnOp -> String
unOpToSource u = _

binOpToSource :: BinOp -> String
binOpToSource b = _
