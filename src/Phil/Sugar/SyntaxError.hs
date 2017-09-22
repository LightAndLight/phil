{-# language TemplateHaskell #-}

module Phil.Sugar.SyntaxError where

import Control.Lens
import Text.PrettyPrint.ANSI.Leijen

import Phil.ErrorMsg
import Phil.Core.AST.Types

data SyntaxError
  = InvalidInstanceArg Type
  | NoInstanceArgs Type
  | InvalidClassArg Type
  deriving (Eq, Show)

makeClassyPrisms ''SyntaxError

-- syntaxErrorMsg :: AsSyntaxError e => e -> Maybe Doc
-- syntaxErrorMsg = previews _SyntaxError (errorMsg "Syntax error" . toMessage)
syntaxErrorMsg = errorMsg "Syntax error" . toMessage
  where
    toMessage (InvalidInstanceArg ty)
      = hsep
        [ text "Instance head"
        , renderType ty
        , text "may not contain type variables"
        ]
    toMessage (NoInstanceArgs ty)
      = hsep
        [ text "Instance head"
        , renderType ty
        , text "requires at least one argument"
        ]
    toMessage (InvalidClassArg ty)
      = hsep
        [ text "Class head"
        , renderType ty
        , text "may only contain type variables"
        ]
