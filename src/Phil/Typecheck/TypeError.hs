{-# language TemplateHaskell #-}
module Phil.Typecheck.TypeError where

import Control.Lens
import Data.List
import Data.List.NonEmpty (NonEmpty)
import Data.Set (Set)
import Data.Text (unpack)
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import qualified Data.Set as S

import Phil.Core.AST.Identifier
import Phil.Core.AST.Types
import Phil.ErrorMsg
import Phil.Typecheck.Unification

data TypeError
  = VarNotInScope Ident
  | CtorNotInScope Ctor
  | VarAlreadyDefined Ident
  | CtorAlreadyDefined Ctor
  | PatternArgMismatch Ctor Int Int
  | DuplicateTypeSignatures Ident
  | CouldNotDeduce [Type] [Type]
  | NoSuchClass Ctor
  | NoSuchInstance Ctor (NonEmpty Type)
  | NonClassFunction Ctor Ident
  | MissingClassFunctions Ctor (NonEmpty (Ctor, [Ident])) (Set Ident)
  | MissingSuperclassInst
      (Ctor, NonEmpty (Ctor, [Ident]))
      (Ctor, NonEmpty (Ctor, [Ident]))
  | TypeMismatch TypeScheme TypeScheme
  | TUnificationError (UnificationError Type)
  deriving (Eq, Show)

makeClassyPrisms ''TypeError

-- typeErrorMsg :: AsTypeError e => e -> Maybe Doc
-- typeErrorMsg = previews _TypeError toMessage
typeErrorMsg = toMessage
  where
    toMessage (VarNotInScope var)
      = errorMsg "Variable not in scope" $
        hsep
          [ text "Variable"
          , squotes . text . unpack $ getIdent var
          , text "not in scope"
          ]

    toMessage (CtorNotInScope ctor)
      = errorMsg "Constructor not in scope" $
        hsep
          [ text "Constructor"
          , squotes . text . unpack $ getCtor ctor
          , text "not in scope"
          ]

    toMessage (PatternArgMismatch constructor actual expected)
      = errorMsg "Pattern arguments mismatch" $
        hsep
          [ squotes . text . unpack $ getCtor constructor
          , text "was given"
          , text $ show actual
          , text  "arguments, but requires"
          , text $ show expected
          ]

    toMessage (VarAlreadyDefined name)
      = errorMsg "Name already defined" $
        hsep
          [ squotes . text . unpack $ getIdent name
          , text "is already defined"
          ]

    toMessage (CtorAlreadyDefined name)
      = errorMsg "Constructor already defined" $
        hsep
          [ squotes . text . unpack $ getCtor name
          , text "is already defined"
          ]

    toMessage (DuplicateTypeSignatures function)
      = errorMsg "Duplicate type signatures" $
        hsep
          [ text "Type signature for"
          , squotes . text . unpack $ getIdent function
          , text "is defined multiple times"
          ]

    toMessage (CouldNotDeduce targets given)
      = errorMsg "Constraint error" $
        hsep
          [ text "Could not deduce"
          , renderConstraints targets
          , text "from"
          , renderConstraints given
          ]

    toMessage (NoSuchClass className)
      = errorMsg "Class not found" $
        hsep
          [ text "Class"
          , squotes . text . unpack $ getCtor className
          , text "cannot be found"
          ]

    toMessage (NoSuchInstance className args)
      = errorMsg "Instance not found" $
        hsep
          [ text "Could not find instance"
          , squotes . renderType $ toType (className, args)
          , text "for class"
          , squotes . text . unpack $ getCtor className
          ]
    toMessage (NonClassFunction className function)
      = errorMsg "Invalid instance definition" $ 
        hsep
          [ squotes . text . unpack $ getIdent function
          , text "is not a member of the"
          , squotes . text . unpack $ getCtor className
          , text "class"
          ]

    toMessage (MissingClassFunctions className args notImplemented)
      = errorMsg "Invalid instance definition" $
        hsep
          [ text "Instance"
          , squotes . renderType $
              toType (className, toTypeTyVars <$> args)
          , text "does not implement required functions:"
          , hcat . intersperse (comma <> space) .
              fmap (text . unpack . getIdent) . S.toList $ notImplemented
          ]

    toMessage (MissingSuperclassInst target required)
      = errorMsg "Invalid instance definition" $
        hsep
          [ text "Could not find instance"
          , squotes (renderType . toType $ over (_2.mapped) toTypeTyVars required) <> 
              text "."
          , brackets $ hsep
              [ text "Required by"
              , squotes . renderType .
                  toType $ over (_2.mapped) toTypeTyVars target
              ]
          ]

    toMessage (TypeMismatch actual expected)
      = errorMsg "Type mismatch" $
        vcat
          [ hsep
            [ text "Expected:"
            , renderTypeScheme expected
            ]
          , hsep
            [ text "Actual:"
            , renderTypeScheme actual
            ]
          ]

    toMessage (TUnificationError (CannotUnify ty ty'))
      = errorMsg "Type error" $
        vcat
          [ text "Cannot unify"
          , text ""
          , renderType ty
          , text "with"
          , hsep [renderType ty']
          ]

    toMessage (TUnificationError (Occurs var ty))
      = errorMsg "Type error" $
        hsep
          [ text "Cannot constuct infinite type"
          , squotes $ hsep [text . unpack $ getIdent var, text "=", renderType ty]
          ]
