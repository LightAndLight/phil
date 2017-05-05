{-# language FlexibleContexts #-}

module Lambda.Typecheck.Module (loadModule, checkModule) where

import GHC.Stack
import Lambda.Exception

import Control.Lens hiding ((<.>))
import Control.Monad.Except
import Control.Monad.Fresh
import Control.Monad.State
import Data.Foldable
import Data.Monoid
import Data.List.NonEmpty (NonEmpty)
import System.FilePath

import qualified Data.List.NonEmpty as N
import qualified Data.Set as S

import Lambda.AST.Binding
import Lambda.AST.Definitions
import Lambda.AST.Modules
import Lambda.Core.AST.Identifier
import Lambda.Core.AST.InstanceHead
import Lambda.Core.AST.ProdDecl
import Lambda.Core.Kinds
import Lambda.Lexer
import Lambda.Lexer.LexError
import Lambda.Parser
import Lambda.Parser.ParseError
import Lambda.Sugar
import Lambda.Sugar.SyntaxError
import Lambda.Typecheck
import Lambda.Typecheck.TypeError
import Lambda.Typeclasses

import qualified Lambda.Core.AST.Expr as C

loadModule
  :: ( AsLexError e
     , AsParseError e
     , MonadError e m
     , MonadIO m
     )
  => FilePath -- ^ Absolute path to base module directory
  -> NonEmpty Identifier -- ^ Module name
  -> m (Module [Definition])
loadModule baseDir modName = do
  contents <- liftIO . readFile $ baseDir </> toModulePath modName
  tokens <- tokenize contents
  parseModule tokens

-- | Check that some module exports intersect with the supplied definitions
--
-- If the module exports are Nothing then all the definitions are considered
-- exported
validateExports
  :: ( HasCallStack
     , HasContext s
     , MonadState s m
     , AsTypeError e
     , MonadError e m
     ) 
  => Maybe (NonEmpty Identifier)
  -> [Definition]
  -> m (Maybe (NonEmpty Identifier))
validateExports exports defs
  = let exportedNames = S.fromList $ foldr getExportedName [] defs
    in case exports of
      Nothing
        | exportedNames /= S.empty
        -> pure . Just . N.fromList $ S.toList exportedNames

        | otherwise 
        -> pure Nothing

      Just names
        | S.fromList (N.toList names) `S.isSubsetOf` exportedNames
        -> pure $ Just names

        | otherwise
        -> throwError $ _NotInScope # N.head names

  where
    getExportedName :: Definition -> [Identifier] -> [Identifier]
    getExportedName def names = case def of
      Data _ _ prods -> N.toList (fmap prodName prods) <> names
      Function binding -> bindingName binding : names
      ValidClass _ className _ _ -> className : names
      ValidInstance _ instHead _ _ -> instanceName instHead : names
      Class{} -> internalError $ InvalidDefinitionException def
      Instance{} -> internalError $ InvalidDefinitionException def
      _ -> names

-- | Check that a module is well-formed
--
-- Requires the imports are in scope
--
-- 1. Checks definitions
-- 2. Checks exports are in scope
-- 3. If the module specified no exports then dumps all names into exports
checkModule
  :: ( MonadFresh m
     , HasKindTable s
     , HasContext s
     , HasTypesignatures s
     , HasTcContext C.Expr s
     , MonadState s m
     , AsLexError e
     , AsParseError e
     , AsTypeError e
     , AsKindError e
     , AsSyntaxError e
     , MonadError e m
     , MonadIO m
     )
  => FilePath -- ^ Absolute path to the base module directory
  -> NonEmpty Identifier -- ^ Module name
  -> m (Module [Definition])
checkModule baseDir modName = do
  mod <- loadModule baseDir modName

  let actualModName = mod ^. moduleName
  when (modName /= actualModName) $
    throwError $ _ModuleNameMismatch # (modName, actualModName)
  
  mod' <- traverse checkDefinitions =<<
          traverseOf (traverse.traverse) desugar mod

  exports <- validateExports
    (mod' ^. moduleExports)
    (mod' ^. moduleData)

  pure (mod' & moduleExports .~ exports)
