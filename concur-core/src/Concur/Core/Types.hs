{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE KindSignatures             #-}
module Concur.Core.Types
  ( Widget(..)
  , continue
  , widget
  , display
  , mapView
  , wrapView
  , Suspend(..)
  , SuspendF(..)
  , Effect
  , effect
  , MultiAlternative(..)
  , loadWithIO
  , awaitIOAction
  , remoteWidget
  , unsafeBlockingIO
  ) where

import           Concur.Core.Notify       (Notify, await, newNotify, newNotifyIO, notify)
import           Control.Applicative      (Alternative, empty, (<|>))
import           Control.Concurrent       (forkIO)
import           Control.Concurrent.STM   (STM, atomically, retry)
import           Control.Monad            (MonadPlus (..))
import           Control.Monad.Free       (Free (..), hoistFree, liftF)
import           Control.Monad.IO.Class   (MonadIO, liftIO)
import           Control.MonadSTM         (MonadSTM (..))
import           Control.MultiAlternative (MultiAlternative, orr, never)

newtype Widget v m a = Widget { suspend :: Free (Suspend v m) a }
  deriving (Functor, Applicative, Monad)

newtype Suspend v (m :: * -> *) a = Suspend { unSuspend :: m (SuspendF v m a) }
  deriving Functor

data SuspendF v (m :: * -> *) a = SuspendF { view :: v, cont :: Effect a }
  deriving Functor

type Effect a = STM (Maybe a)

continue :: Functor m => Suspend v m a -> Widget v m a
continue = Widget . liftF

widget :: Monad m => v -> Effect a -> Widget v m a
widget v r = continue $ Suspend $ return $ SuspendF v r

display :: Monad m => v -> Widget v m a
display v = widget v retry

-- Change the view of a Widget
mapView :: Functor m => (u -> v) -> Widget u m a -> Widget v m a
mapView f (Widget w) = Widget $ go w
  where
    go = hoistFree g
    g (Suspend io) = Suspend $ fmap h io
    h (SuspendF v c) = SuspendF (f v) c

-- Generic widget view wrapper
wrapView :: Functor m => Applicative f => (u -> v) -> Widget u m a -> Widget (f v) m a
wrapView f = mapView (pure . f)

-- A pure effect
effect :: Monad m => v -> STM a -> Widget v m a
effect v m = widget v $ Just <$> m

instance (Monoid v, Monad m) => MonadSTM (Widget v m) where
  liftSTM = effect mempty

-- | IMPORTANT: Blocking IO is dangerous as it can block the entire UI from updating.
--   It should only be used for *very* quick running IO actions like creating MVars.
unsafeBlockingIO :: Monoid v => IO a -> Widget v IO a
unsafeBlockingIO io = continue $ Suspend $ fmap (SuspendF mempty . return . Just) io

-- This is a safe use for blockingIO, and is exported
awaitIOAction :: (Notify a -> v) -> Widget v IO a
awaitIOAction f = continue $ Suspend $ do
  n <- newNotifyIO
  return $ SuspendF (f n) (fmap Just (await n))

loadWithIO :: v -> IO a -> Widget v IO a
loadWithIO v io = continue $ Suspend $ do
  n <- newNotifyIO
  _ <- forkIO $ io >>= atomically . notify n
  return $ SuspendF v (Just <$> await n)

-- Make a Widget, which can be pushed to remotely
remoteWidget :: (MultiAlternative m, MonadSTM m, Monad m) => m b -> (a -> m b) -> STM (a -> m (), m b)
remoteWidget d f = do
  var <- newNotify
  return (proxy var, wid var d)
  where
    proxy var = \a -> liftSTM $ notify var a
    wid var ui = orr [Left <$> ui, Right <$> (liftSTM $ await var)] >>= either return (wid var . f)

instance Monoid v => MonadIO (Widget v IO) where
  liftIO = loadWithIO mempty

-- IMPORTANT NOTE: This Alternative instance is NOT the same one as that for Free.
-- That one simply uses Alternative for Suspend. But that one isn't sufficient for us.
-- Verify laws:
--         Right distributivity (of <*>):  (f <|> g) <*> a = (f <*> a) <|> (g <*> a)
--         Right absorption (for <*>):  empty <*> a = empty
--         Left distributivity (of fmap):  f <$> (a <|> b) = (f <$> a) <|> (f <$> b)
--  OK     Left absorption (for fmap):  f <$> empty = empty
instance (Monad m, Monoid v) => Alternative (Widget v m) where
  empty = never
  f <|> g = orr [f,g]

instance (Monad m, Monoid v) => MultiAlternative (Widget v m) where
  never = display mempty
  orr = Widget . comb . map suspend
    where
      peelAllFree []           = Right []
      peelAllFree (Pure a : _) = Left a
      peelAllFree (Free s: fs) = fmap (s:) $ peelAllFree fs
      comb wfs = case peelAllFree wfs of
        Left a -> pure a
        Right fsio -> Free $ Suspend $ do
          fs <- mapM unSuspend fsio
          return $ SuspendF (mconcat $ map view fs) (merge $ map cont fs)
        where
          merge ws = do
            (i, me) <- foldl (\prev (i,w) -> prev <|> fmap (i,) w) retry $ zip [0..] ws
            return $ fmap (\e -> comb $ take i wfs ++ [e] ++ drop (i+1) wfs) me

-- The default instance derives from Alternative
instance (Monad m, Monoid v) => MonadPlus (Widget v m)
