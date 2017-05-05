{-# language GeneralizedNewtypeDeriving #-}
{-# language TemplateHaskell #-}

module Lambda.Typecheck.TC
  ( TC
  , runTC
  , getModuleInfo
  , addContextEntry
  , addTypesig
  , addKindEntry
  , addClassEntry
  , freeInContext
  , freshDictvar
  , freshKindvar
  , freshTyvar
  , getClassContext
  , ifErrorIn
  , lookupKind
  , lookupType
  , subContext
  , subKindContext
  , tcError
  ) where

import Control.Lens
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Map (Map)
import Data.List.NonEmpty (NonEmpty)
import Data.Set (Set)

import qualified Data.Map as M

import Lambda.Core.AST.Identifier
import Lambda.Core.AST.Kinds
import Lambda.Core.AST.Types
import Lambda.ModuleInfo
import Lambda.Typecheck.KindError
import Lambda.Typecheck.TypeclassEntry
import Lambda.Typecheck.TypeError
import Lambda.Typecheck.Unification

import qualified Lambda.AST.Expr as L
import qualified Lambda.Core.AST.Expr as C

-- | Sorts of entries that could exist in the context
data EntryType
  -- | Overloaded function entry
  = OEntry
  -- | Constructor entry
  | CEntry
  -- | Function entry
  | FEntry
  -- | Recursive entry
  | REntry

data ContextEntry
  = ContextEntry
  { _ceModule :: NonEmpty Identifier
  , _ceEntryType :: EntryType
  , _ceTypeScheme :: TypeScheme
  }

makeLenses ''ContextEntry

data TCState
  = TCState
  { _tcsTypeContext :: Map Identifier ContextEntry
  , _tcsTypesigs :: Map Identifier TypeScheme
  , _tcsKindContext :: Map Identifier Kind
  , _tcsClassContext :: [TypeclassEntry C.Expr]
  , _tcsTyvarCount :: Int
  , _tcsKindvarCount :: Int
  , _tcsDictvarCount :: Int
  }

makeLenses ''TCState

data TCEnv
  = TCEnv
  { _tceModuleInfo :: ModuleInfo
  }

makeLenses ''TCEnv

-- | The typechecker monad. It can return an error or a result.
newtype TC e a
  = TC { unTC :: ReaderT TCEnv (ExceptT e (State TCState)) a }
  deriving (Functor, Applicative, Monad)

initialTCState :: TCState
initialTCState
  = TCState
  { _tcsTypeContext = M.empty
  , _tcsTypesigs = M.empty
  , _tcsKindContext = M.fromList
    [ ("Int", Star)
    , ("Bool", Star)
    , ("String", Star)
    , ("Char", Star)
    ]
  , _tcsClassContext = []
  , _tcsTyvarCount = 0
  , _tcsKindvarCount = 0
  , _tcsDictvarCount = 0
  }

initialTCEnv :: ModuleInfo -> TCEnv
initialTCEnv modInfo
  = TCEnv
  { _tceModuleInfo = modInfo
  }

-- | Run a typechecking computation
runTC :: ModuleInfo -> TC e a -> Either e a
runTC modInfo
  = flip evalState initialTCState .
    runExceptT .
    flip runReaderT (initialTCEnv modInfo) .
    unTC

-- | Throw an error
tcError :: e -> TC e a
tcError = TC . lift . throwError

-- | Runs the first computation if the second throws an error
ifErrorIn :: TC e a -> TC e a -> TC e a
ifErrorIn backup toRun = TC $ do
  env <- ask
  lift $ catchError
    (runReaderT (unTC toRun) env)
    (const $ runReaderT (unTC backup) env)

-- | Retreive the module info that the typechecker is using
getModuleInfo :: TC e ModuleInfo
getModuleInfo = TC (view tceModuleInfo)

-- | Add an entry to the type context
addContextEntry :: Identifier -> EntryType -> TypeScheme -> TC e ()
addContextEntry name entryType scheme = do
  modInfo <- getModuleInfo 
  let entry = ContextEntry (modInfo ^. miModuleName) entryType scheme
  TC . lift . lift $ modify (tcsTypeContext . at name .~ Just entry)

-- | Register a type signature for a name
addTypesig :: Identifier -> TypeScheme -> TC e ()
addTypesig name scheme
  = TC . lift . lift $ modify (tcsTypesigs . at name .~ Just scheme)

-- | Add an entry to the kind context
addKindEntry :: Identifier -> Kind -> TC e ()
addKindEntry name kind
  = TC . lift . lift $ modify (tcsKindContext . at name .~ Just kind)

-- | Add a typeclass entry
addClassEntry :: TypeclassEntry C.Expr -> TC e ()
addClassEntry entry
  = TC . lift . lift $ modify (over tcsClassContext (entry :))

-- | Apply a substitution to the type context
subContext :: Substitution Type -> TC e ()
subContext subs
  = TC . lift . lift $
    modify (over (tcsTypeContext.mapped.ceTypeScheme) (subTypeScheme subs))

-- | Apply a substitution to the kind context
subKindContext :: Substitution Kind -> TC e ()
subKindContext subs
  = TC . lift . lift $
    modify (over (tcsKindContext.mapped) (substitute subs))

-- | Look up an entry in the type context. Throws 'NotInScope' if not found.
lookupType :: AsTypeError e => Identifier -> TC e ContextEntry
lookupType name = TC $ do
  maybeTy <- lift . lift $ use (tcsTypeContext . at name)
  case maybeTy of
    Just ty -> pure ty
    Nothing -> throwError $ _NotInScope # name

-- | Look up an entry in the kind context. Throws 'KNotDefined' if not found.
lookupKind :: AsKindError e => Identifier -> TC e Kind
lookupKind name = TC $ do
  maybeKind <- lift . lift $ use (tcsKindContext . at name)
  case maybeKind of
    Just kind -> pure kind
    Nothing -> throwError $ _KNotDefined # name

-- | Generate a fresh type variable
freshTyvar :: TC e Type
freshTyvar = TC . lift . lift $ do
  n <- use tcsTyvarCount
  tcsTyvarCount += 1
  pure . TyVar $ "t" ++ show n

-- | Generate a fresh kind variable
freshKindvar :: TC e Kind
freshKindvar = TC . lift . lift $ do
  n <- use tcsKindvarCount
  tcsKindvarCount += 1
  pure . KindVar $ "k" ++ show n

-- | Generate a fresh dictionary variable
freshDictvar :: TC e L.Expr
freshDictvar = do
  modName <- _miModuleName <$> getModuleInfo
  TC . lift . lift $ do
    n <- use tcsDictvarCount
    tcsDictvarCount += 1
    pure . L.DictVar (Just modName) $ "dict" ++ show n

-- | Calculate all the free variables in the context
freeInContext :: TC e (Set Identifier)
freeInContext
  = TC . lift . lift .
    uses tcsTypeContext $
    foldMapOf (folded.ceTypeScheme) freeInScheme

-- | Retreives the current typeclass context
getClassContext :: TC e [TypeclassEntry C.Expr]
getClassContext = TC . lift . lift $ use tcsClassContext
