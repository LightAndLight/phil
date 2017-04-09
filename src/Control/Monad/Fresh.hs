{-# language FlexibleInstances #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language MultiParamTypeClasses #-}
{-# language UndecidableInstances #-}

module Control.Monad.Fresh
  ( runFreshT
  , module Fresh
  ) where

import Control.Monad.Except
import Control.Monad.Free
import Control.Monad.Fresh.Class as Fresh
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans
import Control.Monad.Writer

newtype FreshT m a = FreshT { runFreshT' :: StateT Int m a }
  deriving (Functor, Applicative, Monad)

instance MonadError e m => MonadError e (FreshT m) where
  throwError = FreshT . throwError
  catchError (FreshT m) f = FreshT $ catchError m (runFreshT' . f)

instance (Functor f, MonadFree f m) => MonadFree f (FreshT m) where

instance MonadState s m => MonadState s (FreshT m) where
  get = FreshT $ lift get
  put = FreshT . lift . put

instance MonadReader r m => MonadReader r (FreshT m) where
  ask = FreshT ask
  local f (FreshT m) = FreshT $ local f m

instance MonadWriter w m => MonadWriter w (FreshT m) where
  writer = FreshT . writer
  listen (FreshT m) = FreshT $ listen m
  pass (FreshT m) = FreshT $ pass m

instance Monad m => MonadFresh (FreshT m) where
  reset = FreshT $ put 0
  fresh = FreshT $ do
    n <- get 
    put (n + 1)
    pure $ show n

instance MonadTrans FreshT where
  lift = FreshT . lift

runFreshT :: Monad m => FreshT m a -> m a
runFreshT (FreshT st) = evalStateT st 0
