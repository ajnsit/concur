{-# LANGUAGE RankNTypes            #-}
module Control.MonadTransMap where

import           Control.Monad.State          (StateT, mapStateT)
import           Control.Monad.Trans.Identity (IdentityT, mapIdentityT)

class MonadTransMap t where
  liftMap :: (forall x. m x -> m x) -> t m a -> t m a

instance MonadTransMap IdentityT where
  liftMap = mapIdentityT

instance MonadTransMap (StateT s) where
  liftMap = mapStateT
