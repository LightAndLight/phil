{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
module Phil.PHP.AST
  ( PHP(..)
  , PHPId
  , phpId
  , unPHPId
  , PHPDecl(..)
  , PHPClassMember(..)
  , Visibility(..)
  , PHPExpr(..)
  , PHPArg(..)
  , UnOp(..)
  , BinOp(..)
  , PHPStatement(..)
  , PHPSwitchCase (..)
  , PHPDefaultCase (..)
  , PHPLiteral(..)
  )
  where

import Control.Lens
import Data.Monoid
import Data.String
import Data.Text (Text, pack)

data PHP = PHP [PHPDecl]
newtype PHPId = PHPId { unPHPId :: Text }
  deriving (Eq, Show, Ord)

phpId :: Text -> PHPId
phpId input = PHPId $ go input
  where
    go i = case uncons i of
      Nothing -> ""
      Just ('\'', rest) -> "Prime" <> go rest
      Just (c, rest) -> cons c $ go rest

instance IsString PHPId where
  fromString = phpId . pack

data PHPDecl
  = PHPDeclFunc PHPId [PHPArg] [PHPStatement]
  | PHPDeclClass PHPId [PHPClassMember]
  | PHPDeclStatement PHPStatement
data PHPClassMember
  = PHPClassFunc Bool Visibility PHPId [PHPArg] [PHPStatement]
  | PHPClassVar Bool Visibility PHPId (Maybe PHPExpr)
data Visibility = Public | Protected | Private
data PHPArg
  = PHPArgValue PHPId
  | PHPArgReference PHPId
  deriving (Eq, Ord)
data PHPExpr
  = PHPExprVar PHPId
  | PHPExprNew PHPId [PHPExpr]
  | PHPExprLiteral PHPLiteral
  | PHPExprBinop BinOp PHPExpr PHPExpr
  | PHPExprUnop UnOp PHPExpr
  | PHPExprAssign PHPExpr PHPExpr
  | PHPExprFunction [PHPArg] [PHPArg] [PHPStatement]
  | PHPExprClassAccess PHPExpr PHPId (Maybe [PHPExpr])
  | PHPExprArrayAccess PHPExpr PHPExpr
  | PHPExprFunctionCall PHPExpr [PHPExpr]
  | PHPExprName PHPId
data UnOp
  = Negate
  | Not
data BinOp
  = Add
  | Subtract
  | Multiply
  | Divide
  | Mod
  | Exp
  | Equal
  | NotEqual
  | Less
  | Greater
  | LessEq
  | GreaterEq
  | And
  | Or
  | Concat
  | InstanceOf
data PHPStatement
  = PHPStatementReturn PHPExpr
  | PHPStatementSwitch PHPExpr [PHPSwitchCase] PHPDefaultCase
  | PHPStatementThrow PHPExpr
  | PHPStatementExpr PHPExpr
  | PHPStatementIfThenElse PHPExpr [PHPStatement] (Maybe [PHPStatement])
data PHPSwitchCase = PHPSwitchCase PHPLiteral [PHPStatement] Bool
data PHPDefaultCase = PHPDefaultCase [PHPStatement] Bool
data PHPLiteral
  = PHPBool Bool
  | PHPInt Integer
  | PHPString String
  | PHPNull
  | PHPArray [PHPExpr]
