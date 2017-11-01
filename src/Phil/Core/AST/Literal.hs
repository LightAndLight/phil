module Phil.Core.AST.Literal where

import Text.PrettyPrint.ANSI.Leijen

data Literal
  = LitInt Integer
  | LitString String
  | LitChar Char
  | LitBool Bool
  deriving (Eq, Show)

renderLiteral :: Literal -> Doc
renderLiteral (LitInt a) = text $ show a
renderLiteral (LitString a) = text $ show a
renderLiteral (LitChar a) = text $ show a
renderLiteral (LitBool b) = text $ if b then "true" else "false"
