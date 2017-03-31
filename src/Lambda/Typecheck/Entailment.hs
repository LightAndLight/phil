{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

module Lambda.Typecheck.Entailment ( buildDicts, entails ) where

import Debug.Trace

import           Data.Bifunctor
import           Data.Monoid
import           Data.Foldable
import           Control.Applicative
import           Data.Maybe

import           Lambda.Core.AST.Evidence
import           Lambda.Core.AST.Types
import           Lambda.Typecheck.Unification
import           Lambda.Typeclasses

{-
findEntry :: Type -> TypeclassEntry -> Maybe (TypeclassEntry, Substitution Type)
findEntry pi entry@(TceInst supers ty _) =
  case unify [(ty, pi)] of
    Left _ -> Nothing
    Right sub -> Just (entry, sub)
findEntry pi entry@(TceClass supers ty _) = (,) entry <$> asum (flip equiv pi <$> supers)
-}

findEntry :: Type -> TypeclassEntry a -> Maybe (TypeclassEntry a, Substitution Type)
findEntry pi entry@(TceInst supers ty _) = (,) entry <$> equiv ty pi
findEntry pi entry@(TceClass supers ty _) = (,) entry <$> asum (flip equiv pi <$> supers)

-- | Dis is broken
equiv :: Type -> Type -> Maybe (Substitution Type)
equiv (TyVar ty) ty'@TyVar{} = Just $ Substitution [(ty, ty')]
equiv (TyApp t1 t2) (TyApp t1' t2') = do
  t1Subs <- equiv t1 t1'
  t2Subs <- equiv t2 t2'
  if all (\(s1, s2) -> fst s1 /= fst s2 || snd s1 == snd s2) $
    zip (getSubstitution t1Subs) (getSubstitution t2Subs)
    then Just $ t1Subs <> t2Subs
    else Nothing
equiv ty ty'
  | ty == ty' = Just mempty
  | otherwise = Nothing

entails :: [TypeclassEntry a] -> [(Dictionary, Type)] -> Type -> Maybe Dictionary
entails entries ps pi
  | ((d, _):_) <- filter (\p -> snd p == traceShowId pi) (traceShowId ps) = Just d
  | otherwise = go (catMaybes $ findEntry pi <$> entries)
  where
    go :: [(TypeclassEntry a, Substitution Type)] -> Maybe Dictionary
    go [] = Nothing
    go ((TceInst supers ty _, sub) : rest) = do 
      dicts <- sequence (entails entries ps . substitute sub <$> supers)
      pure $ if null dicts
        then Dict pi
        else Construct pi dicts
    go ((TceClass supers ty _, sub) : rest) =
      (Select pi <$> entails entries ps (substitute sub ty)) <|> go rest

buildDicts :: [TypeclassEntry a] -> [(EVar, Type)] -> [(EVar, Dictionary)]
buildDicts entries ps = go ps
  where
    ps' = first Variable <$> ps

    go [] = []
    go ((var, ty) : rest) =
      let res = entails entries [] ty <|> entails entries (filter ((/= ty) . snd) ps') ty <|> entails entries ps' ty
      in (var, fromJust res) : go rest
