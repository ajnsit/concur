{-# LANGUAGE RankNTypes #-}
module Concur.Free where

import           Control.Monad.Free

-------------------------------------
-- UTILITIES FOR DEALING WITH FREE --
-------------------------------------

mapAllSuspensions :: (Functor t) => (forall x. s x -> t x) -> Free s a -> Free t a
mapAllSuspensions = hoistFree

combineFree
     :: (r1 -> Free s2 r2 -> a)
     -> (Free s1 r1 -> r2 -> a)
     -> (s1 (Free s1 r1) -> s2 (Free s2 r2) -> a)
     -> Free s1 r1
     -> Free s2 r2
     -> a
combineFree retmL _ _  (Pure fa) g         = retmL fa g
combineFree _ retmR _  f         (Pure ga) = retmR f ga
combineFree _ _ combLR (Free fs) (Free gs) = combLR fs gs

tearFree :: (f (Free f a) -> t) -> (f (Free f a) -> Free f a) -> Free f a -> [t]
tearFree a b = go
  where
  go (Pure _) = []
  go (Free f) = a f : go (b f)
