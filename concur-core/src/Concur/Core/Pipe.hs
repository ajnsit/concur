{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}
module Concur.Core.Pipe where

import Data.Void (Void)

import Concur.Core.Types (Widget, never)
import Control.MultiAlternative
import Control.MonadShiftMap

import Control.Applicative (Alternative, (<|>))

-------------------------------------------------------
-- NOTE: This is buggy and has terrible performance. --
--               Don't use this yet.                 --
-------------------------------------------------------

data Pipe m a b = Pipe
  -- Need a Maybe around `b` because the pipe may change internally without an output
  { pipeOut  :: m ((Maybe b, Pipe m a b))
  , pipeIn :: a -> Pipe m a b
  }

ffor :: Functor m => m a -> (a -> b) -> m b
ffor = flip fmap

runPipe :: Monad m => Pipe m Void b -> m x
runPipe p = pipeOut p >>= runPipe . snd

liftPipe :: Functor m => m b -> Pipe m x b
liftPipe m = go where go = Pipe (ffor m $ \ma -> (Just ma, go)) (const go)

pipeHold :: Functor m => (a -> m b) -> m b -> Pipe m a b
pipeHold f = go
  where
    go w = Pipe (ffor w $ \b -> (Just b, go w)) $ go . f

-- infixr >->
(>->) :: (Alternative m, Monad m) => Pipe m a b -> Pipe m b c -> Pipe m a c
(>->) pa pb = Pipe (m pa pb) (f pa pb)
  where
    m pa' pb' = do
      er <- (Left <$> pipeOut pa') <|> (Right <$> pipeOut pb')
      case er of
        Left (Just b, pa'') -> do
          let pb'' = pipeIn pb' b
          return (Nothing, pa'' >-> pb'')
        Left (Nothing, pa'') -> do
          return (Nothing, pa'' >-> pb')
        Right (Nothing, pb'') -> do
          return (Nothing, pa' >-> pb'')
        Right (Just c, pb'') -> do
          return (Just c, pa' >-> pb'')
    f pa' pb' a = Pipe (m pa' pb') (f (pipeIn pa' a) pb')

(<-<) :: (Alternative m, Monad m) => Pipe m b c -> Pipe m a b -> Pipe m a c
(<-<) = flip (>->)

instance Monoid v => MultiAlternative (Pipe (Widget v) a) where
  orr ps = Pipe (orr (map pipeOut ps)) (\a -> orr (map (flip pipeIn a) ps))

instance MonadShiftMap (Widget v) (Pipe (Widget v) a) where
  shiftMap f (Pipe r c) = Pipe (f r) (shiftMap f <$> c)

-- Pure Pipe - this is fine
purePipe :: Monoid v => (a -> b) -> Pipe (Widget v) a b
purePipe f = go never
  where
    go w = Pipe w (\a -> go (return (Just (f a), go never)))

statefulPipe :: Monoid v => (s -> a -> (s, b)) -> s -> Pipe (Widget v) a b
statefulPipe f sinit = go sinit never
  where
    go s w = Pipe w (g s)
    g s a = let (s', b) = f s a in go s' (return (Just b, go s' never))

-- Util: Function -> Kleisli
kleisli :: Monad m => (a -> b) -> a -> m b
kleisli f = return . f
