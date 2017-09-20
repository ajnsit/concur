{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}
module Control.MonadShiftMap where

import           Control.Natural              (type (~>))

import           Control.Monad.State          (StateT, mapStateT)
import           Control.Monad.Trans.Identity (IdentityT, mapIdentityT)

-- | Mapping between Natural Transformations
class MonadShiftMap s t where
  shiftMap :: (s ~> s) -> (t ~> t)

instance MonadShiftMap m m where
  shiftMap = id

instance MonadShiftMap m (IdentityT m) where
  shiftMap = mapIdentityT

instance MonadShiftMap m (StateT s m) where
  shiftMap = mapStateT
