module Phil.Core.AST.Pattern where

import           Phil.Core.AST.Identifier
import           Phil.Core.AST.Literal

data Pattern
  = PatId Identifier
  | PatCon Identifier [Identifier]
  | PatLit Literal
  | PatWildcard
  deriving (Eq, Show)

showPattern :: Pattern -> String
showPattern (PatId a) = a
showPattern (PatCon name args) = name ++ unwords args
showPattern (PatLit lit) = showLiteral lit
