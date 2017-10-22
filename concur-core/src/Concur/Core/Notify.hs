module Concur.Core.Notify
  ( Notify
  , fetch
  , await
  , notify
  , newNotify
  , newNotifyIO
  ) where

import           Control.Concurrent.STM (STM, TVar, newTVar, newTVarIO,
                                         readTVar, retry, writeTVar)
import           Control.Monad          (void)

-- TODO: Use Weak TVar pointers as appropriate
newtype Notify a = Notify (TVar (Maybe a))

fetch :: Notify a -> STM (Maybe a)
fetch (Notify v) = tryTakeTVar v

await :: Notify a -> STM a
await (Notify v) = takeTVar v

notify :: Notify a -> a -> STM ()
notify (Notify v) a = void (writeTVar v (Just a))

newNotify :: STM (Notify a)
newNotify = Notify <$> newTVar Nothing

newNotifyIO :: IO (Notify a)
newNotifyIO = Notify <$> newTVarIO Nothing

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
