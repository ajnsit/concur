{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
module Control.MonadShiftMap where

import           Control.MonadTransMap

-- | Lateral mapping. Generalises `MonadTransMap`.
-- TODO: I'm sure some Lens concept maps to this
class MonadShiftMap s t where
  shiftMap :: (forall x. s x -> s x) -> t a -> t a

instance MonadShiftMap m m where
  shiftMap = id

instance MonadTransMap t => MonadShiftMap m (t m) where
  shiftMap = liftMap
