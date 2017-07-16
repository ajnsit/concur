module Concur.Notify
  ( Notify (..)
  , newNotify
  ) where

import           Control.Concurrent (newEmptyMVar, takeMVar, tryPutMVar)
import           Control.Monad      (void)

data Notify a = Notify
  { await  :: IO a
  , notify :: a -> IO ()
  }

newNotify :: IO (Notify a)
newNotify = do
  mvar <- newEmptyMVar
  pure $ Notify
   (takeMVar mvar)
   (void . tryPutMVar mvar)
