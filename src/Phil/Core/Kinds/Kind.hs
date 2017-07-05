{-# language TypeFamilies #-}

module Phil.Core.Kinds.Kind where

import           Phil.Core.AST.Identifier
import           Phil.Typecheck.Unification

data Kind
  = Star
  | KindArrow Kind Kind
  | KindVar Identifier
  | Constraint
  deriving (Eq, Show, Ord)

instance Unify Kind where
  type Variable Kind = Identifier

  substitute (Substitution []) k = k
  substitute subs (KindArrow k1 k2) = KindArrow (substitute subs k1) (substitute subs k2)
  substitute (Substitution ((var, t') : rest)) t@(KindVar var')
    | var == var' = t'
    | otherwise = substitute (Substitution rest) t
  substitute _ t = t

  implications (k@KindVar{}, k') = [(k, k')]
  implications (k, k'@KindVar{}) = [(k', k)]
  implications (KindArrow k1 k2, KindArrow k1' k2')
    = let i1 = implications (k1, k1')
          i2 = implications (k2, k2')
      in if null i1 || null i2 then [] else i1 ++ i2
  implications c@(k, k')
    | k == k' = [c]
    | otherwise = []

  occurs name (KindVar name') = name == name'
  occurs name (KindArrow k1 k2) = occurs name k1 || occurs name k2
  occurs _ _ = False

  toVariable (KindVar name) = Just name
  toVariable _ = Nothing

showKind :: Kind -> String
showKind Star = "*"
showKind Constraint = "Constraint"
showKind (KindArrow k1 k2) = unwords [nested k1, "->", showKind k2]
  where
    nested k@KindArrow{} = "(" ++ showKind k ++ ")"
    nested k = showKind k
showKind (KindVar name) = name

-- If we don't instantiate the result of kind inference then we have Kind Polymorphism
instantiateKind :: Kind -> Kind
instantiateKind (KindArrow k1 k2) = KindArrow (instantiateKind k1) (instantiateKind k2)
instantiateKind Constraint = Constraint
instantiateKind _ = Star
