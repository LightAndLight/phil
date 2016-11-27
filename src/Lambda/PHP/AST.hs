module Lambda.PHP.AST where

data PHP = PHP [PHPDecl]
newtype PHPId = PHPId { unPHPId :: String }
data PHPDecl
  = PHPDeclFunc PHPId [PHPId] [PHPStatement]
  | PHPDeclClass PHPId [PHPClassMember]
  | PHPDeclExpr PHPExpr
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
  = PHPReturn PHPExpr
  | PHPSwitch PHPExpr [PHPSwitchCase] PHPDefaultCase
data PHPSwitchCase = PHPSwitchCase PHPLiteral [PHPStatement] Bool
data PHPDefaultCase = PHPDefaultCase [PHPStatement] Bool
data PHPLiteral
  = PHPBool Bool
  | PHPInt Int
  | PHPString String
  | PHPNull
  | PHPArray [PHPExpr]
