module Concur.Notify
  ( Notify (..)
  , newNotify
  ) where

import           Control.Concurrent.STM (STM, TVar, newTVar, readTVar, writeTVar, retry)
import           Control.Monad          (void)

-- TODO: Use Weak TVar pointers as appropriate
data Notify a = Notify
  { fetch  :: STM (Maybe a)
  , await  :: STM a
  , notify :: a -> STM ()
  }

newNotify :: STM (Notify a)
newNotify = do
  v <- newTVar Nothing
  return $ Notify
   (tryTakeTVar v)
   (takeTVar v)
   (void . writeTVar v . Just)

takeTVar :: TVar (Maybe a) -> STM a
takeTVar t = do
  m <- readTVar t
  case m of
    Nothing -> retry
    Just a  -> do writeTVar t Nothing; return a

tryTakeTVar :: TVar (Maybe a) -> STM (Maybe a)
tryTakeTVar t = do
  m <- readTVar t
  case m of
    Nothing -> return Nothing
    Just a  -> do writeTVar t Nothing; return (Just a)
