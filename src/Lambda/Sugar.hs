{-# language FlexibleContexts #-}
module Lambda.Sugar where

import           Data.List.NonEmpty (NonEmpty(..))
import Control.Monad.State
import Control.Monad.Error
import Control.Applicative
import Control.Lens
import Data.Monoid
import qualified Data.Set as S
import qualified Data.Map as M

import qualified Lambda.Core        as C
import Lambda

data Declaration
  = Data C.Identifier [C.Identifier] (NonEmpty C.ProdDecl)
  | Function { functionName :: C.Identifier, functionArgs :: [C.Pattern], functionValue :: C.Expr }

data PatternFunction = PatternFunction C.Identifier (NonEmpty C.Pattern) C.Expr

toPatternFunction :: Declaration -> Either Declaration PatternFunction
toPatternFunction (Function name (a:as) expr) = Right $ PatternFunction name (a :| as) expr
toPatternFunction d = Left d

translateDeclarations :: (HasSymbolTable s, MonadState s m, MonadError InferenceError m) => [Declaration] -> m [C.Declaration]
translateDeclarations [] = pure []
translateDeclarations (d:decls) = case d of
  (Data tyCon tyVars cons) -> (C.Data tyCon tyVars cons :) <$> translateDeclarations decls
  (Function name args value) -> do
    let (same,rest) = span (getAll . (All . hasArgs <> All . sameFunction name)) decls
    unless (all ((==) (length args) . length . functionArgs) rest) . throwError $ FunctionArgMismatch name
    bound <- uses symbolTable M.keysSet
    when (name `S.member` bound) . throwError $ AlreadyDefined name
    let absVars = take (length args) . filter (not . flip S.member bound) $ fmap ((++) "a" . show) [1..]
    let translatedCase = buildExpr (fmap toPatternFunction $ d :| same) absVars
    (C.Binding name (foldr C.Abs translatedCase absVars) :) <$> translateDeclarations rest
  where
    sameFunction name (Function name' _ _) = name == name'
    sameFunction _ _ = False

    hasArgs (Function _ args _) = not $ null args
    hasArgs _ = False

    samePattern (PatternFunction )

    buildExpr ((PatternFunction name (arg :| args) expr) :| fs) argNames = let (samePattern,rest) = span
