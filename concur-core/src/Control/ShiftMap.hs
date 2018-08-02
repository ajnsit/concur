{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}
module Control.ShiftMap where

import           Control.Natural              (type (~>))

import           Control.Monad.State          (StateT, mapStateT)
import           Control.Monad.Trans.Identity (IdentityT, mapIdentityT)

-- | Mapping between Natural Transformations
class ShiftMap s t where
  shiftMap :: (s ~> s) -> (t ~> t)

instance ShiftMap m m where
  shiftMap = id

instance ShiftMap m (IdentityT m) where
  shiftMap = mapIdentityT

instance ShiftMap m (StateT s m) where
  shiftMap = mapStateT
