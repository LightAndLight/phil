{-# language TemplateHaskell #-}

module Lambda.Sugar.SyntaxError where

import Control.Lens
import Text.PrettyPrint

import Lambda.ErrorMsg
import Lambda.Core.AST.Types

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
      = hsep $ text <$>
        [ "Instance head"
        , showType ty
        , "may not contain type variables"
        ]
    toMessage (NoInstanceArgs ty)
      = hsep $ text <$>
        [ "Instance head"
        , showType ty
        , "requires at least one argument"
        ]
    toMessage (InvalidClassArg ty)
      = hsep $ text <$>
        [ "Class head"
        , showType ty
        , "may only contain type variables"
        ]
