module Lambda.Typecheck.Contraints where

import Lambda.Core.AST.Kinds
import Lambda.Core.AST.Types
import Lambda.Typecheck.KindError
import Lambda.Typecheck.Kind
import Lambda.Typecheck.TC
import Lambda.Typecheck.TypeclassEntry
import Lambda.Typecheck.Unification

checkConstraints :: AsKindError e => [Type] -> TC e (Substitution Kind)
checkConstraints [] = pure mempty
checkConstraints [con] = do
  (subs, k) <- inferKind con
  either (tcError . review _KUnificationError) (const $ pure subs) $ unify [(k, Constraint)]
checkConstraints (con:rest) = do
  subs <- checkConstraints [con]
  substituteKindContext subs 
  subs' <- checkConstraints rest
  pure $ subs' <> subs
