module Lambda.PHP.AST
  ( PHP(..)
  , PHPId
  , phpId
  , unPHPId
  , PHPDecl(..)
  , PHPClassMember(..)
  , Visibility(..)
  , PHPExpr(..)
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
newtype PHPId = PHPId { unPHPId :: String }

phpId :: String -> PHPId
phpId input = PHPId $ go input
  where
    go "" = ""
    go ('\'':rest) = "Prime" ++ go rest
    go (c:rest) = c : go rest

instance IsString PHPId where
  fromString = phpId

data PHPDecl
  = PHPDeclFunc PHPId [PHPId] [PHPStatement]
  | PHPDeclClass PHPId [PHPClassMember]
  | PHPDeclStatement PHPStatement
data PHPClassMember
  = PHPClassFunc Bool Visibility PHPId [PHPId] [PHPStatement]
  | PHPClassVar Bool Visibility PHPId (Maybe PHPExpr)
data Visibility = Public | Protected | Private
data PHPExpr
  = PHPExprVar PHPId
  | PHPExprNew PHPId
  | PHPExprLiteral PHPLiteral
  | PHPExprBinop BinOp PHPExpr PHPExpr
  | PHPExprUnop UnOp PHPExpr
  | PHPExprAssign PHPId PHPExpr
  | PHPExprFunction [PHPId] [PHPStatement]
  | PHPExprClassAccess PHPId PHPId (Maybe [PHPExpr])
  | PHPExprFunctionCall PHPExpr [PHPExpr]
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
data PHPStatement
  = PHPStatementReturn PHPExpr
  | PHPStatementSwitch PHPExpr [PHPSwitchCase] PHPDefaultCase
  | PHPStatementThrow PHPExpr
  | PHPStatementExpr PHPExpr
data PHPSwitchCase = PHPSwitchCase PHPLiteral [PHPStatement] Bool
data PHPDefaultCase = PHPDefaultCase [PHPStatement] Bool
data PHPLiteral
  = PHPBool Bool
  | PHPInt Int
  | PHPString String
  | PHPNull
  | PHPArray [PHPExpr]
