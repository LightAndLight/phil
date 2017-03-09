module Lambda.Core.Typecheck.Substitution where

import           Data.Map                   (Map)
import qualified Data.Map                   as M
import           Data.Maybe

import           Lambda.Core.AST.Identifier
import           Lambda.Core.AST.Types

type Substitution = Map Identifier Type

substitute :: Substitution -> Type -> Type
substitute subs ty@(TyVar name) = fromMaybe ty $ M.lookup name subs
substitute subs (TyApp from to) = TyApp (substitute subs from) (substitute subs to)
substitute subs ty = ty

-- apply s1 to s2
applySubs :: Substitution -> Substitution -> Substitution
applySubs s1 = M.union s1 . fmap (substitute s1)

subTypeScheme :: Substitution -> TypeScheme -> TypeScheme
subTypeScheme subs (Forall vars cons ty) = Forall vars cons $ substitute (foldr M.delete subs vars) ty

subContext :: Substitution -> Map Identifier TypeScheme -> Map Identifier TypeScheme
subContext subs = fmap (subTypeScheme subs)
