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

lineWords :: [String] -> SourceM ()
lineWords = line . unwords

line :: String -> SourceM ()
line input = do
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
  line ""
  traverse phpDeclToSource decls
  line "?>"

variable :: PHPId -> String
variable name = "$" <> unPHPId name

functionArgsToSource :: [PHPId] -> String
functionArgsToSource = intercalate ", " . fmap variable

phpDeclToSource :: PHPDecl -> SourceM ()
phpDeclToSource (PHPDeclFunc name args body) = do
  lineWords ["function", unPHPId name <> bracketed (functionArgsToSource args), "{"]
  indented $ traverse phpStatementToSource body
  line "}"
  line ""
phpDeclToSource (PHPDeclClass name members) = do
  lineWords ["class", unPHPId name, "{"]
  indented $ traverse phpClassMemberToSource members
  line "}"
  line ""
phpDeclToSource (PHPDeclStatement st) = do
  phpStatementToSource st
  line ""

bracketed :: String -> String
bracketed input = "(" <> input <> ")"

functionValuesToSource :: [PHPExpr] -> SourceM String
functionValuesToSource = fmap (bracketed . intercalate ", ") . traverse phpExprToSource

phpExprToSource :: PHPExpr -> SourceM String
phpExprToSource (PHPExprVar name) = return $ variable name
phpExprToSource (PHPExprName name) = return $ unPHPId name
phpExprToSource (PHPExprNew className args) = do
  args' <- functionValuesToSource args
  return $ "new " <> unPHPId className <> args'
phpExprToSource (PHPExprLiteral lit) = phpLiteralToSource lit
phpExprToSource (PHPExprClassAccess var memberName args) = do
  var' <- phpExprToSource var
  args' <- maybe (return "") functionValuesToSource args
  return $ var' <> "->" <> unPHPId memberName <> args'
phpExprToSource (PHPExprArrayAccess array index) = do
  array' <- phpExprToSource array
  index' <- phpExprToSource index
  return $ array' <> "[" <> index' <> "]"
phpExprToSource (PHPExprBinop op left right) = do
  left' <- phpExprToSource left
  right' <- phpExprToSource right
  return $ unwords
    [ case left of
        PHPExprBinop{} -> bracketed left'
        _ -> left'
    , binOpToSource op
    , case right of
        PHPExprBinop{} -> bracketed right'
        _ -> right'
    ]
phpExprToSource (PHPExprUnop op arg) = do
  arg' <- phpExprToSource arg
  return $ unOpToSource op <> bracketed arg'
phpExprToSource (PHPExprAssign left expr) = do
  left' <- phpExprToSource left
  expr' <- phpExprToSource expr
  return $ unwords
    [ left'
    , "="
    , expr'
    ]
phpExprToSource (PHPExprFunction args use body) = do
  added <- linesAdded . indented $ traverse phpStatementToSource body
  bracket <- linesAdded $ line "}"
  let useVars = case use of
        [] -> ""
        use -> " use " <> bracketed (functionArgsToSource use)
  return $ "function" <> bracketed (functionArgsToSource args) <> useVars <> " {\n" <>
    (unlines . toList $ added) <>
    (head . toList $ bracket)
phpExprToSource (PHPExprFunctionCall func args) = do
  func' <- phpExprToSource func
  let functionPart = case func of
        PHPExprVar{} -> func'
        PHPExprFunctionCall{} -> func'
        PHPExprName{} -> func'
        _ -> bracketed func'
  args' <- traverse phpExprToSource args
  pure $ functionPart <> bracketed (intercalate "," args')

visibilityToSource :: Visibility -> String
visibilityToSource Public = "public"
visibilityToSource Private = "private"
visibilityToSource Protected = "protected"

classMemberPrefix :: Bool -> Visibility -> [String]
classMemberPrefix True visibility = [visibilityToSource visibility, "static"]
classMemberPrefix False visibility = [visibilityToSource visibility]

phpClassMemberToSource :: PHPClassMember -> SourceM ()
phpClassMemberToSource (PHPClassFunc static visibility name args body) = do
  lineWords $ classMemberPrefix static visibility <> ["function", unPHPId name <> bracketed (functionArgsToSource args) <> " {"]
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
phpStatementToSource (PHPStatementReturn expr) = do
  expr' <- phpExprToSource expr
  semicolon line $ unwords ["return", expr']
phpStatementToSource (PHPStatementSwitch cond switches def) = do
  cond' <- phpExprToSource cond
  lineWords ["switch", bracketed cond', "{"]
  indented $ do
    traverse phpSwitchCaseToSource switches
    phpDefaultCaseToSource def
  line "}"
phpStatementToSource (PHPStatementIfThenElse cond ifTrue ifFalse) = do
  cond' <- phpExprToSource cond
  lineWords ["if", bracketed cond', "{"]
  indented $ traverse phpStatementToSource ifTrue
  case ifFalse of
    Nothing -> pure ()
    Just falseStatements -> do
      line "else {"
      indented $ traverse phpStatementToSource falseStatements
  line "}"
phpStatementToSource (PHPStatementThrow expr) = do
  expr' <- phpExprToSource expr
  semicolon line $ unwords ["throw", expr']
phpStatementToSource (PHPStatementExpr expr) = semicolon line =<< phpExprToSource expr

phpLiteralToSource :: PHPLiteral -> SourceM String
phpLiteralToSource (PHPBool b) = return $ if b then "true" else "false"
phpLiteralToSource (PHPInt n) = return $ show n
phpLiteralToSource (PHPString str) = return $ "\"" <> str <> "\""
phpLiteralToSource PHPNull = return "null"
phpLiteralToSource (PHPArray vals) = do
  vals' <- traverse phpExprToSource vals
  return $ "array" <> bracketed (intercalate ", " vals')

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
binOpToSource InstanceOf = "instanceof"
