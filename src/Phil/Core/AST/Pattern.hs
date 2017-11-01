module Phil.Core.AST.Pattern where

import Data.Monoid
import Data.Text (Text)

import qualified Data.Text as T

import Phil.Core.AST.Identifier
import Phil.Core.AST.Literal

import Text.PrettyPrint.ANSI.Leijen hiding ((<>))

data Pattern
  = PatId Ident
  | PatCon Ctor [Ident]
  | PatLit Literal
  | PatWildcard
  deriving (Eq, Show)

renderPattern :: Pattern -> Doc
renderPattern (PatId a) = text . T.unpack $ getIdent a
renderPattern (PatCon name args) =
  text . T.unpack $ getCtor name <> T.unwords (fmap getIdent args)
renderPattern (PatLit lit) = renderLiteral lit
renderPattern PatWildcard = text "_"
