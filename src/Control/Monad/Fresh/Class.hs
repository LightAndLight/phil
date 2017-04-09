module Control.Monad.Fresh.Class where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer

class Monad m => MonadFresh m where
  reset :: m ()
  fresh :: m String

instance MonadFresh m => MonadFresh (ExceptT e m) where
  reset = lift reset
  fresh = lift fresh

instance MonadFresh m => MonadFresh (ReaderT r m) where
  reset = lift reset
  fresh = lift fresh

instance MonadFresh m => MonadFresh (StateT s m) where
  reset = lift reset
  fresh = lift fresh

instance (Monoid w, MonadFresh m) => MonadFresh (WriterT w m) where
  reset = lift reset
  fresh = lift fresh
