{-# language TemplateHaskell #-}

module Phil.Core.Kinds.KindError where

import Control.Lens
import Data.Text (unpack)
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import Phil.Core.AST.Identifier
import Phil.Core.Kinds.Kind
import Phil.ErrorMsg
import Phil.Typecheck.Unification

data KindError
  = KVarNotDefined Ident
  | KCtorNotDefined Ctor
  | KUnificationError (UnificationError Kind)
  deriving (Eq, Show)

makeClassyPrisms ''KindError

-- kindErrorMsg :: AsKindError e => e -> Maybe Doc
-- kindErrorMsg = previews _KindError (errorMsg "Kind error" . msgBody)
kindErrorMsg = errorMsg "Kind error" . msgBody
  where
    msgBody (KVarNotDefined name)
      = hsep $ text <$>
          [ "Variable"
          , unpack $ getIdent name
          , "not in scope"
          ]

    msgBody (KCtorNotDefined name)
      = hsep $ text <$>
          [ "Type constructor"
          , unpack $ getCtor name
          , "not in scope"
          ]

    msgBody (KUnificationError (CannotUnify k k'))
      = vcat
          [ hsep [text "Cannot unify", renderKind k]
          , text "with"
          , hsep [renderKind k']
          ]

    msgBody (KUnificationError (Occurs var k))
      = hsep
          [ text "Cannot constuct infinite kind"
          , squotes $ hsep [text . unpack $ getIdent var, text "=", renderKind k]
          ]
