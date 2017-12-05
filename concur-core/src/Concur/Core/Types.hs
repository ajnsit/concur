{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE RankNTypes                 #-}
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
  , awaitSTMAction
  , awaitNotification
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
import           Control.Monad.Trans      (MonadTrans(..))

newtype Widget v m a = Widget { suspend :: Free (Suspend v m) a }
  deriving (Functor, Applicative, Monad)

newtype Suspend v (m :: * -> *) a = Suspend { unSuspend :: m (SuspendF v m a) }
  deriving Functor

data SuspendF v (m :: * -> *) a = SuspendF { view :: v, cont :: Effect a }
  deriving Functor

type Effect a = STM (Maybe a)

instance Monoid v => MonadTrans (Widget v) where
  lift = continue . Suspend . fmap (SuspendF mempty . return . Just)

continue :: Functor m => Suspend v m a -> Widget v m a
continue = Widget . liftF

widget :: Applicative m => v -> Effect a -> Widget v m a
widget v r = continue $ Suspend $ pure $ SuspendF v r

display :: Applicative m => v -> Widget v m a
display v = widget v retry

-- Util
mapViewSuspend :: Functor m => (u -> v) -> Suspend u m a -> Suspend v m a
mapViewSuspend f (Suspend io) = Suspend $ fmap (h f) io
  where
    h f' (SuspendF v c) = SuspendF (f' v) c

-- Change the view of a Widget
mapView :: Functor m => (u -> v) -> Widget u m a -> Widget v m a
mapView f (Widget w) = Widget $ hoistFree (mapViewSuspend f) w

-- Generic widget view wrapper
wrapView :: (Functor m, Applicative f) => (u -> v) -> Widget u m a -> Widget (f v) m a
wrapView f = mapView (pure . f)

-- A pure effect
effect :: Applicative m => v -> STM a -> Widget v m a
effect v m = widget v $ Just <$> m

-- We want a different MonadSTM instance, instead of the default one which relies on (MonadTrans (Widget v), MonadSTM m)
-- The default one is basically (forkIO . atomically), and thus unnecessarily forks, when we provide native STM effects.
instance {-# OVERLAPS #-} (Monad m, Monoid v) => MonadSTM (Widget v m) where
  liftSTM = effect mempty

-- | IMPORTANT: Blocking IO is dangerous as it can block the entire UI from updating.
--   It should only be used for *very* quick running IO actions like creating MVars.
unsafeBlockingIO :: (Applicative m, Monoid v) => m a -> Widget v m a
unsafeBlockingIO io = continue $ Suspend $ fmap (SuspendF mempty . pure . Just) io

-- This is a safe use for blockingIO, and is exported
awaitSTMAction :: (Monad m, MonadSTM m) => (Notify a -> v) -> Widget v m a
awaitSTMAction f = continue $ Suspend $ do
  n <- liftSTM newNotify
  return $ SuspendF (f n) (fmap Just (await n))

-- This is a safe use for blockingIO, and is exported
awaitNotification :: (Monad m, MonadSTM m) => v -> (Notify a -> Widget v m b) -> Widget v m b
awaitNotification v f = Widget $ Free $ Suspend $ do
  n <- liftSTM newNotify
  case f n of
    Widget (Free (Suspend m)) -> m
    Widget ret@(Pure _) -> return $ SuspendF v (return $ Just ret)

-- This is safe beacuse of the fork, and is exported
loadWithIO :: MonadIO m => v -> IO a -> Widget v m a
loadWithIO v io = continue $ Suspend $ do
  n <- liftIO $ do
    n <- newNotifyIO
    _ <- forkIO (io >>= atomically . notify n)
    return n
  return $ SuspendF v (Just <$> await n)

-- Similarly this instance is safe
instance Monoid v => MonadIO (Widget v IO) where
  liftIO = loadWithIO mempty

-- Make a Widget, which can be pushed to remotely
remoteWidget :: (MultiAlternative m, MonadSTM m, Monad m) => m b -> (a -> m b) -> STM (a -> m (), m b)
remoteWidget d f = do
  var <- newNotify
  return (proxy var, wid var d)
  where
    proxy var = \a -> liftSTM $ notify var a
    wid var ui = orr [Left <$> ui, Right <$> (liftSTM $ await var)] >>= either return (wid var . f)

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
