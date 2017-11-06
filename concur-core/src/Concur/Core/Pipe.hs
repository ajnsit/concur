{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}
module Concur.Core.Pipe where

import Data.Void (Void, absurd)

import Control.Monad (forever)
import Control.Monad.Trans (MonadTrans, lift)

import Concur.Core.Types (Widget, never)
import Control.MultiAlternative
import Control.MonadShiftMap

import Control.Applicative (Alternative, (<|>), empty)

type Consumer m a = Pipe m a Void
type Producer m b = Pipe m Void b

data Pipe m a b = Pipe
  { pipeIn  :: a -> m b
  , pipeOut :: m b
  } deriving Functor

runPipe :: Monad m => Pipe m Void Void -> m x
runPipe p = forever $ pipeOut p

infixl >->
(>->) :: (Alternative m, Monad m) => Pipe m a b -> Pipe m b c -> Pipe m a c
(>->) (Pipe fa mb) (Pipe fb mc) = Pipe (\a -> m (fa a) mc) (m mb mc)
  where
    m mb' mc' = (fmap Left mb' <|> fmap Right mc') >>= either (m mb' . fb) return

infixr <-<
(<-<) :: (Alternative m, Monad m) => Pipe m b c -> Pipe m a b -> Pipe m a c
(<-<) = flip (>->)

pipe :: MultiAlternative m => (a -> m b) -> Pipe m a b
pipe f = Pipe f never

produce :: m b -> Producer m b
produce m = Pipe absurd m

shiftPipe :: (forall x. m x -> n x) -> Pipe m a b -> Pipe n a b
shiftPipe f (Pipe c r) = Pipe (f <$> c) (f r)

liftPipe :: (MonadTrans t, Monad m) => Pipe m a b -> Pipe (t m) a b
liftPipe = shiftPipe lift

purePipe :: (MultiAlternative m, Applicative m) => (a -> b) -> Pipe m a b
purePipe = pipe . kleisli

-- instance MultiAlternative m => Alternative (Pipe m a) where
--   empty = never
--   f <|> g = orr [f,g]

instance MultiAlternative m => MultiAlternative (Pipe m a) where
  never = Pipe (const never) never
  orr ps = Pipe (\a -> orr (map (flip pipeIn a) ps)) (orr (map pipeOut ps))

instance MonadShiftMap (Widget v) m => MonadShiftMap (Widget v) (Pipe m a) where
  shiftMap f = shiftPipe (shiftMap f)

-- Util: Function -> Kleisli
kleisli :: Applicative m => (a -> b) -> a -> m b
kleisli f = pure . f

-- Util: Ffor
ffor :: Functor m => m a -> (a -> b) -> m b
ffor = flip fmap
