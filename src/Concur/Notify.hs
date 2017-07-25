module Concur.Notify
  ( Notify (..)
  , newNotify
  ) where

import           Control.Concurrent.STM (STM, TVar, newTVar, readTVar, writeTVar)
import           Control.Monad          (void)

data Notify a = Notify
  { fetch  :: STM (Maybe a)
  , notify :: a -> STM ()
  }

newNotify :: STM (Notify a)
newNotify = do
  v <- newTVar Nothing
  return $ Notify
   (tryTakeTVar v)
   (void . writeTVar v . Just)

tryTakeTVar :: TVar (Maybe a) -> STM (Maybe a)
tryTakeTVar t = do
  m <- readTVar t
  case m of
    Nothing -> return Nothing
    Just a  -> do writeTVar t Nothing; return (Just a)
