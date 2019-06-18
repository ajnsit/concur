module Concur.Core.Notify
  ( Notify
  , fetch
  , await
  , notify
  , newNotify
  ) where

import           Control.Concurrent
import           Control.Monad          (void)

-- TODO: Use Weak TVar pointers as appropriate
newtype Notify a = Notify (MVar a)

fetch :: Notify a -> IO (Maybe a)
fetch (Notify v) = tryTakeMVar v

await :: Notify a -> IO a
await (Notify v) = takeMVar v

notify :: Notify a -> a -> IO ()
notify (Notify v) a = void (putMVar v a)

newNotify :: IO (Notify a)
newNotify = Notify <$> newEmptyMVar