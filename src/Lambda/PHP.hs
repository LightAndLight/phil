{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell            #-}

module Lambda.PHP (toSource) where

import           Control.Lens        (makeLenses, use, (%=), (+=), (-=), (.=))
import           Control.Monad.State
import           Data.DList          (DList, empty, snoc, toList)
import           Data.Foldable       (traverse_)
import           Data.List           (intercalate)
import           Data.Monoid

import           Lambda.PHP.AST

data SourceState = SourceState { _indentSequence :: String, _indentLevel :: Int, _output :: DList String }
makeLenses ''SourceState

newtype SourceM a = SourceM { unSourceM :: State SourceState a }
  deriving (Functor, Applicative, Monad, MonadState SourceState)

toSource :: String -> PHP -> String
toSource indentSeq php
  = unlines .
    toList $
    evalState (unSourceM $ phpToSource php >> use output) (SourceState indentSeq 0 empty)

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
  output %= flip snoc (join (replicate level indentSeq) <> input <> "\n")

line' :: String -> SourceM ()
line' input = do
  level <- use indentLevel
  indentSeq <- use indentSequence
  output %= flip snoc (join (replicate level indentSeq) <> input)

semicolon :: (String -> SourceM a) -> String -> SourceM a
semicolon f s = f (s <> ";")

linesAdded :: SourceM a -> SourceM (DList String)
linesAdded source = do
  initial <- use output
  output .= empty
  source
  result <- use output
  output .= initial
  return result

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
  traverse phpDeclToSource decls
  line "?>"

variable :: PHPId -> String
variable name = "$" <> unPHPId name

functionArgsToSource :: [PHPId] -> String
functionArgsToSource = intercalate ", " . fmap variable

phpDeclToSource :: PHPDecl -> SourceM ()
phpDeclToSource (PHPDeclFunc name args body) = do
  line $ "function " <> unPHPId name <> "(" <> functionArgsToSource args <> ") {"
  indented $ traverse phpStatementToSource body
  line "}"
phpDeclToSource (PHPDeclClass name members) = do
  line $ "class " <> unPHPId name <> " {"
  indented $ traverse phpClassMemberToSource members
  line "}"
phpDeclToSource (PHPDeclExpr expr) = semicolon line =<< phpExprToSource expr
phpDeclToSource (PHPDeclStatement st) = phpStatementToSource st

bracketed :: String -> String
bracketed input = "(" <> input <> ")"

phpExprToSource :: PHPExpr -> SourceM String
phpExprToSource (PHPExprVar name) = return $ variable name
phpExprToSource (PHPExprNew className) = return $ "new " <> unPHPId className
phpExprToSource (PHPExprLiteral lit) = phpLiteralToSource lit
phpExprToSource (PHPExprBinop op left right) = do
  left' <- phpExprToSource left
  right' <- phpExprToSource right
  return $ unwords
    [ bracketed left'
    , binOpToSource op
    , bracketed right'
    ]
phpExprToSource (PHPExprUnop op arg) = do
  arg' <- phpExprToSource arg
  return $ unOpToSource op <> bracketed arg'
phpExprToSource (PHPExprAssign name expr) = do
  expr' <- phpExprToSource expr
  return $ unwords
    [ variable name
    , "="
    , expr'
    ]
phpExprToSource (PHPExprFunction args body) = do
  added <- linesAdded . indented $ traverse phpStatementToSource body
  bracket <- linesAdded $ line' "}"
  return $ "function(" <> functionArgsToSource args <> ") {\n" <>
    (unlines . toList $ added) <>
    (head . toList $ bracket)

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
phpClassMemberToSource (PHPClassVar static visibility name value) = do
  value' <- case value of
    Just e -> do
      e' <- phpExprToSource e
      return ["=", e']
    Nothing -> return []
  line . unwords $ classMemberPrefix static visibility <> [variable name] <> value'

phpSwitchCaseToSource :: PHPSwitchCase -> SourceM ()
phpSwitchCaseToSource (PHPSwitchCase match body br) = do
  match' <- phpLiteralToSource match
  line $ "case " <> match' <> ":"
  indented $ do
    traverse phpStatementToSource body
    when br . semicolon line $ "break"

phpDefaultCaseToSource :: PHPDefaultCase -> SourceM ()
phpDefaultCaseToSource (PHPDefaultCase body br) = do
  line "default:"
  indented $ do
    traverse phpStatementToSource body
    when br . semicolon line $ "break"

phpStatementToSource :: PHPStatement -> SourceM ()
phpStatementToSource (PHPReturn expr) = do
  expr' <- phpExprToSource expr
  semicolon line $ "return " <> expr'
phpStatementToSource (PHPSwitch cond switches def) = do
  cond' <- phpExprToSource cond
  line $ "switch (" <> cond' <> ") {"
  indented $ do
    traverse phpSwitchCaseToSource switches
    phpDefaultCaseToSource def
  line "}"

phpLiteralToSource :: PHPLiteral -> SourceM String
phpLiteralToSource (PHPBool b) = return $ if b then "true" else "false"
phpLiteralToSource (PHPInt n) = return $ show n
phpLiteralToSource (PHPString str) = return $ "\"" <> str <> "\""
phpLiteralToSource PHPNull = return "null"
phpLiteralToSource (PHPArray vals) = do
  vals' <- traverse phpExprToSource vals
  return $ "array(" <> intercalate ", " vals' <> ")"

unOpToSource :: UnOp -> String
unOpToSource Negate = "-"
unOpToSource Not = "!"

binOpToSource :: BinOp -> String
binOpToSource Add = "+"
binOpToSource Subtract = "-"
binOpToSource Multiply = "*"
binOpToSource Divide = "/"
binOpToSource Mod = "%"
binOpToSource Exp = "**"
binOpToSource Equal = "==="
binOpToSource NotEqual = "!=="
binOpToSource Less = "<"
binOpToSource Greater = ">"
binOpToSource LessEq = "<="
binOpToSource GreaterEq = ">="
binOpToSource And = "&&"
binOpToSource Or = "||"
binOpToSource Concat = "."
