{-# LANGUAGE FlexibleInstances #-}
module Control.MonadSTM where

import           Control.Concurrent.STM (STM)
import           Control.Monad.Trans    (MonadTrans (..))

-- | Like `MonadIO` but for `STM` monad
-- `MonadBase` seemed too cumbersome for this.
class MonadSTM m where
  liftSTM :: STM a -> m a

instance (MonadTrans t, Monad m, MonadSTM m) => MonadSTM (t m) where
  liftSTM = lift . liftSTM
