{-# language TemplateHaskell #-}

module Phil.Core.Kinds.KindError where

import Control.Lens
import Text.PrettyPrint

import           Phil.Core.AST.Identifier
import           Phil.Core.Kinds.Kind
import           Phil.ErrorMsg
import           Phil.Typecheck.Unification

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
