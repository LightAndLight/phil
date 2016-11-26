module Lambda.PHP.AST where

data PHP = PHP [PHPDecl]
newtype PHPId = PHPId { unPHPId :: String }
data PHPDecl
  = PHPDeclFunc PHPId [PHPId] [PHPStatement]
  | PHPDeclClass PHPId [PHPClassMember]
  | PHPDeclExpr PHPExpr
data PHPClassMember
  = PHPClassFunc Bool Visibility PHPId [PHPStatement]
  | PHPClassVar Bool Visibility PHPId PHPExpr
data Visibility = Public | Protected | Private
data PHPExpr
  = PHPExprVar PHPId
  | PHPExprNew PHPId
  | PHPExprLiteral PHPLiteral
  | PHPExprBinop BinOp PHPLiteral PHPLiteral
  | PHPExprUnop UnOp PHPLiteral
  | PHPExprAssign PHPId PHPExpr
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
  | Xor
  | Concat
data PHPStatement
  = PHPReturn PHPExpr
  | PHPSwitch PHPExpr [PHPSwitchCase] PHPDefaultCase
data PHPSwitchCase = PHPSwitchCase PHPLiteral [PHPStatement] Bool
data PHPDefaultCase = PHPDefaulCase [PHPStatement] Bool
data PHPLiteral
  = PHPBool Bool
  | PHPInt Int
  | PHPString String
  | PHPNull
  | PHPArray [PHPExpr]
