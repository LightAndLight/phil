{-# language TemplateHaskell #-}

module Lambda.Typecheck.TypeError where

import Control.Applicative
import Control.Lens
import Data.List
import Data.List.NonEmpty (NonEmpty)
import qualified Data.Set as S
import Data.Set (Set)
import Text.PrettyPrint

import Lambda.Core.AST.Identifier
import Lambda.Core.AST.InstanceHead
import Lambda.Core.AST.Types
import Lambda.ErrorMsg
import Lambda.Typecheck.Unification

data TypeError
  = NotInScope Identifier
  | PatternArgMismatch Identifier Int Int
  | AlreadyDefined Identifier
  | DuplicateTypeSignatures Identifier
  | CouldNotDeduce [Type] [Type]
  | NoSuchClass Identifier
  | NoSuchInstance Identifier (NonEmpty Type)
  | NonClassFunction Identifier Identifier
  | MissingClassFunctions Identifier (NonEmpty (Identifier, [Identifier])) (Set Identifier)
  | MissingSuperclassInst
      (Identifier, NonEmpty (Identifier, [Identifier]))
      (Identifier, NonEmpty (Identifier, [Identifier]))
  | TypeMismatch TypeScheme TypeScheme
  | TUnificationError (UnificationError Type)
  deriving (Eq, Show)

makeClassyPrisms ''TypeError

-- typeErrorMsg :: AsTypeError e => e -> Maybe Doc
-- typeErrorMsg = previews _TypeError toMessage
typeErrorMsg = toMessage
  where
    toMessage (NotInScope var)
      = errorMsg "Variable not in scope" $
        hsep
          [ text "Variable"
          , quotes $ text var
          , text "not in scope"
          ]

    toMessage (PatternArgMismatch constructor actual expected)
      = errorMsg "Pattern arguments mismatch" $
        hsep
          [ quotes $ text constructor
          , text "was given"
          , text $ show actual
          , text  "arguments, but requires"
          , text $ show expected
          ]
        
    toMessage (AlreadyDefined name)
      = errorMsg "Name already defined" $
        hsep
          [ quotes $ text name
          , text "is already defined in this file"
          ]

    toMessage (DuplicateTypeSignatures function)
      = errorMsg "Duplicate type signatures" $
        hsep
          [ text "Type signature for"
          , quotes $ text function
          , text "is defined multiple times"
          ]

    toMessage (CouldNotDeduce targets given)
      = errorMsg "Constraint error" $
        hsep
          [ text "Could not deduce"
          , text $ showConstraints targets
          , text "from"
          , text $ showConstraints given
          ]

    toMessage (NoSuchClass className)
      = errorMsg "Class not found" $
        hsep
          [ text "Class"
          , quotes $ text className
          , text "cannot be found"
          ]

    toMessage (NoSuchInstance className args)
      = errorMsg "Instance not found" $
        hsep
          [ text "Could not find instance"
          , quotes . text . showType $ toType (className, args)
          , text "for class"
          , quotes $ text className
          ]
    toMessage (NonClassFunction className function)
      = errorMsg "Invalid instance definition" $ 
        hsep
          [ quotes $ text function
          , text "is not a member of the"
          , quotes $ text className
          , text "class"
          ]

    toMessage (MissingClassFunctions className args notImplemented)
      = errorMsg "Invalid instance definition" $
        hsep
          [ text "Instance"
          , quotes . text . showType $
              toType (className, toTypeTyVars <$> args)
          , text "does not implement required functions:"
          , hcat . intersperse (comma <> space) .
              fmap text . S.toList $ notImplemented
          ]

    toMessage (MissingSuperclassInst target required)
      = errorMsg "Invalid instance definition" $
        hsep
          [ text "Could not find instance"
          , quotes (text . showType . toType $ over (_2.mapped) toTypeTyVars required) <> 
              text "."
          , brackets $ hsep
              [ text "Required by"
              , quotes . text . showType .
                  toType $ over (_2.mapped) toTypeTyVars target
              ]
          ]

    toMessage (TypeMismatch actual expected)
      = errorMsg "Type mismatch" $
        vcat
          [ hsep
            [ text "Expected:"
            , text $ showTypeScheme expected
            ]
          , hsep
            [ text "Actual:"
            , text $ showTypeScheme actual
            ]
          ]

    toMessage (TUnificationError (CannotUnify ty ty'))
      = errorMsg "Type error" $
        vcat
          [ text "Cannot unify"
          , text ""
          , text $ showType ty
          , text "with"
          , hsep [text $ showType ty']
          ]

    toMessage (TUnificationError (Occurs var ty))
      = errorMsg "Type error" $
        hsep
          [ text "Cannot constuct infinite type"
          , quotes $ hsep [text var, text "=", text $ showType ty]
          ]
