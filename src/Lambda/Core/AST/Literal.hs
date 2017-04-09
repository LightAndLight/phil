module Lambda.Core.AST.Literal where

data Literal
  = LitInt Int
  | LitString String
  | LitChar Char
  | LitBool Bool
  deriving (Eq, Show)

showLiteral :: Literal -> String
showLiteral (LitInt a) = show a
showLiteral (LitString a) = show a
showLiteral (LitChar a) = show a
showLiteral (LitBool b) = if b then "true" else "false"
