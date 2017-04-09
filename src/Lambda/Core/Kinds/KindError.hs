{-# language TemplateHaskell #-}

module Lambda.Core.Kinds.KindError where

import Control.Lens
import Text.PrettyPrint

import           Lambda.Core.AST.Identifier
import           Lambda.Core.Kinds.Kind
import           Lambda.ErrorMsg
import           Lambda.Typecheck.Unification

data KindError
  = KNotDefined Identifier
  | KUnificationError (UnificationError Kind)
  deriving (Eq, Show)

makeClassyPrisms ''KindError

-- kindErrorMsg :: AsKindError e => e -> Maybe Doc
-- kindErrorMsg = previews _KindError (errorMsg "Kind error" . msgBody)
kindErrorMsg = errorMsg "Kind error" . msgBody
  where
    msgBody (KNotDefined name)
      = hsep $ text <$>
          [ "Variable"
          , name
          , "not in scope"
          ]

    msgBody (KUnificationError (CannotUnify k k'))
      = vcat
          [ hsep [text "Cannot unify", text $ showKind k]
          , text "with"
          , hsep [text $ showKind k']
          ]

    msgBody (KUnificationError (Occurs var k))
      = hsep
          [ text "Cannot constuct infinite kind"
          , quotes $ hsep [text var, text "=", text $ showKind k]
          ]
