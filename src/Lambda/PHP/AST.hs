{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Lambda.PHP.AST
  ( PHP(..)
  , PHPId
  , phpId
  , unPHPId
  , consPHPDecl
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

import           Data.String

data PHP = PHP [PHPDecl]
  deriving (Eq, Show)

consPHPDecl :: PHPDecl -> PHP -> PHP
consPHPDecl decl (PHP decls) = PHP $ decl : decls

newtype PHPId = PHPId { unPHPId :: String }
  deriving (Eq, Show, Ord)

phpId :: String -> PHPId
phpId input = PHPId $ go input
  where
    go "" = ""
    go ('\'':rest) = "Prime" ++ go rest
    go (c:rest) = c : go rest

instance IsString PHPId where
  fromString = phpId

data PHPDecl
  = PHPDeclFunc PHPId [PHPArg] [PHPStatement]
  | PHPDeclClass PHPId [PHPClassMember]
  | PHPDeclStatement PHPStatement
  deriving (Eq, Show)

data PHPClassMember
  = PHPClassFunc Bool Visibility PHPId [PHPArg] [PHPStatement]
  | PHPClassVar Bool Visibility PHPId (Maybe PHPExpr)
  deriving (Eq, Show)

data Visibility = Public | Protected | Private
  deriving (Eq, Show)

data PHPArg
  = PHPArgValue PHPId
  | PHPArgReference PHPId
  deriving (Eq, Ord, Show)

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
  deriving (Eq, Show)

data UnOp
  = Negate
  | Not
  deriving (Eq, Show)

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
  deriving (Eq, Show)

data PHPStatement
  = PHPStatementReturn PHPExpr
  | PHPStatementSwitch PHPExpr [PHPSwitchCase] PHPDefaultCase
  | PHPStatementThrow PHPExpr
  | PHPStatementExpr PHPExpr
  | PHPStatementIfThenElse PHPExpr [PHPStatement] (Maybe [PHPStatement])
  | PHPStatementInclude PHPExpr
  deriving (Eq, Show)

data PHPSwitchCase = PHPSwitchCase PHPLiteral [PHPStatement] Bool
  deriving (Eq, Show)

data PHPDefaultCase = PHPDefaultCase [PHPStatement] Bool
  deriving (Eq, Show)

data PHPLiteral
  = PHPBool Bool
  | PHPInt Int
  | PHPString String
  | PHPNull
  | PHPArray [PHPExpr]
  deriving (Eq, Show)
