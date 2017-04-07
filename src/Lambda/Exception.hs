module Lambda.Exception where

import Control.Exception
import Data.Typeable (Typeable)
import GHC.Stack

instance Exception e => Exception (InternalException e) where

data InternalException e
  = InternalException CallStack e
  deriving Typeable

instance Show e => Show (InternalException e) where
  show (InternalException cs e)
    = unlines
      [ "\n\nInternal Exception. This this a bug.\n" 
      , prettyCallStack cs
      , ""
      , show e
      ]

internalError :: (HasCallStack, Exception e) => e -> a
internalError e
  = throw (InternalException callStack e)
