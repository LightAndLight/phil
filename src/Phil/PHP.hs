{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell            #-}
module Phil.PHP (toSource) where

import Control.Lens (makeLenses, use, (%=), (+=), (-=), (.=))
import Control.Monad.State
import Data.DList (DList, empty, snoc, toList)
import Data.Text (Text)
import Data.Foldable (traverse_)
import Data.Monoid

import qualified Data.Text as T

import Phil.PHP.AST

data SourceState
  = SourceState
  { _indentSequence :: Text
  , _indentLevel :: Int
  , _output :: DList Text
  }
makeLenses ''SourceState

newtype SourceM a = SourceM { unSourceM :: State SourceState a }
  deriving (Functor, Applicative, Monad, MonadState SourceState)

toSource :: Text -> PHP -> Text
toSource indentSeq php
  = T.unlines .
    toList $
    evalState (unSourceM $ phpToSource php >> use output) (SourceState indentSeq 0 empty)

indent :: SourceM ()
indent = indentLevel += 1

dedent :: SourceM ()
dedent = do
  level <- use indentLevel
  when (level > 0) (indentLevel -= 1)

lineWords :: [Text] -> SourceM ()
lineWords = line . T.unwords

line :: Text -> SourceM ()
line input = do
  level <- use indentLevel
  indentSeq <- use indentSequence
  output %= flip snoc (T.replicate level indentSeq <> input)

semicolon :: (Text -> SourceM a) -> Text -> SourceM a
semicolon f s = f (s <> ";")

linesAdded :: SourceM a -> SourceM (DList Text)
linesAdded source = do
  initial <- use output
  output .= empty
  source
  result <- use output
  output .= initial
  return result

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

variable :: PHPId -> Text
variable name = "$" <> unPHPId name

phpArg :: PHPArg -> Text
phpArg (PHPArgValue name) = variable name
phpArg (PHPArgReference name) = "&" <> variable name

phpArgs :: [PHPArg] -> Text
phpArgs = T.intercalate ", " . fmap phpArg

phpDeclToSource :: PHPDecl -> SourceM ()
phpDeclToSource (PHPDeclFunc name args body) = do
  lineWords ["function", unPHPId name <> bracketed (phpArgs args), "{"]
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

bracketed :: Text -> Text
bracketed input = "(" <> input <> ")"

functionValuesToSource :: [PHPExpr] -> SourceM Text
functionValuesToSource = fmap (bracketed . T.intercalate ", ") . traverse phpExprToSource

phpExprToSource :: PHPExpr -> SourceM Text
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
  return $ T.unwords
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
  return $ T.unwords
    [ left'
    , "="
    , expr'
    ]
phpExprToSource (PHPExprFunction args use body) = do
  added <- linesAdded . indented $ traverse phpStatementToSource body
  bracket <- linesAdded $ line "}"
  let useVars = case use of
        [] -> ""
        use -> " use " <> bracketed (phpArgs use)
  return $ "function" <> bracketed (phpArgs args) <> useVars <> " {\n" <>
    (T.unlines . toList $ added) <>
    (head . toList $ bracket)
phpExprToSource (PHPExprFunctionCall func args) = do
  func' <- phpExprToSource func
  let functionPart = case func of
        PHPExprVar{} -> func'
        PHPExprFunctionCall{} -> func'
        PHPExprName{} -> func'
        _ -> bracketed func'
  args' <- traverse phpExprToSource args
  pure $ functionPart <> bracketed (T.intercalate "," args')

visibilityToSource :: Visibility -> Text
visibilityToSource Public = "public"
visibilityToSource Private = "private"
visibilityToSource Protected = "protected"

classMemberPrefix :: Bool -> Visibility -> [Text]
classMemberPrefix True visibility = [visibilityToSource visibility, "static"]
classMemberPrefix False visibility = [visibilityToSource visibility]

phpClassMemberToSource :: PHPClassMember -> SourceM ()
phpClassMemberToSource (PHPClassFunc static visibility name args body) = do
  lineWords $ classMemberPrefix static visibility <> ["function", unPHPId name <> bracketed (phpArgs args) <> " {"]
  indented $ traverse phpStatementToSource body
  line "}"
phpClassMemberToSource (PHPClassVar static visibility name value) = do
  value' <- case value of
    Just e -> do
      e' <- phpExprToSource e
      return ["=", e']
    Nothing -> return []
  line . T.unwords $
    classMemberPrefix static visibility <> [variable name] <> value'

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
  semicolon line $ T.unwords ["return", expr']
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
  semicolon line $ T.unwords ["throw", expr']
phpStatementToSource (PHPStatementExpr expr) = semicolon line =<< phpExprToSource expr

phpLiteralToSource :: PHPLiteral -> SourceM Text
phpLiteralToSource (PHPBool b) = return $ if b then "true" else "false"
phpLiteralToSource (PHPInt n) = return . T.pack $ show n
phpLiteralToSource (PHPString str) = return $ "\"" <> T.pack str <> "\""
phpLiteralToSource PHPNull = return "null"
phpLiteralToSource (PHPArray vals) = do
  vals' <- traverse phpExprToSource vals
  return $ "array" <> bracketed (T.intercalate ", " vals')

unOpToSource :: UnOp -> Text
unOpToSource Negate = "-"
unOpToSource Not = "!"

binOpToSource :: BinOp -> Text
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


test a
  | Just b <- a, b == 0 = 0
  | Just b <- a, b == 1 = 1
  | otherwise = 2
