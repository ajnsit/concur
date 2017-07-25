{-# LANGUAGE RankNTypes #-}
module Data.MonadTransMap where

import Control.Monad.State (StateT, mapStateT)
import Control.Monad.Trans.Identity (IdentityT, mapIdentityT)

class MonadTransMap t where
  liftMap :: (forall a. m a -> m a) -> t m a -> t m a

instance MonadTransMap IdentityT where
  liftMap = mapIdentityT

instance MonadTransMap (StateT s) where
  liftMap = mapStateT
