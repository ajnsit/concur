{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TupleSections              #-}
module Concur.Core.Types
  ( Widget(..)
  , continue
  , widget
  , display
  , never
  , mapView
  , wrapView
  , Suspend
  , view
  , runIO
  , cont
  , Effect
  , effect
  , MultiAlternative(..)
  ) where

import           Concur.Core.Notify       (await, newNotify, notify)
import           Control.Applicative      (Alternative, empty, (<|>))
import           Control.Concurrent       (forkIO)
import           Control.Concurrent.STM   (STM, atomically, retry)
import           Control.Monad            (MonadPlus (..), void)
import           Control.Monad.Free       (Free (..), hoistFree, liftF)
import           Control.Monad.IO.Class   (MonadIO, liftIO)
import           Control.MonadSTM         (MonadSTM (..))
import           Control.MultiAlternative (MultiAlternative, orr)

newtype Widget v a = Widget { suspend :: Free (Suspend v) a }
  deriving (Functor, Applicative, Monad)

data Suspend v a = Suspend { view :: v, runIO :: Maybe (IO ()), cont :: Effect a }
  deriving Functor

type Effect a = STM (Maybe a)

continue :: Suspend v a -> Widget v a
continue = Widget . liftF

widget :: v -> Effect a -> Widget v a
widget v r = continue $ Suspend v Nothing r

display :: v -> Widget v a
display v = widget v retry

-- Never returns, use as an identity for <|>
never :: Monoid v => Widget v a
never = display mempty

-- Change the view of a Widget
mapView :: (u -> v) -> Widget u a -> Widget v a
mapView f (Widget w) = Widget $ go w
  where
    go = hoistFree $ \s -> Suspend (f $ view s) (runIO s) (cont s)

-- Generic widget view wrapper
wrapView :: Applicative f => (u -> v) -> Widget u a -> Widget (f v) a
wrapView f = mapView (pure . f)

-- A pure effect
effect :: v -> STM a -> Widget v a
effect v m = widget v $ Just <$> m

instance Monoid v => MonadSTM (Widget v) where
  liftSTM = effect mempty

instance Monoid v => MonadIO (Widget v) where
  liftIO io = do
    n <- liftSTM newNotify
    continue $ Suspend mempty (Just $ void $ forkIO $ io >>= atomically . notify n) $ Just <$> await n

-- IMPORTANT NOTE: This Alternative instance is NOT the same one as that for Free.
-- That one simply uses Alternative for Suspend. But that one isn't sufficient for us.
-- Verify laws:
--         Right distributivity (of <*>):  (f <|> g) <*> a = (f <*> a) <|> (g <*> a)
--         Right absorption (for <*>):  empty <*> a = empty
--         Left distributivity (of fmap):  f <$> (a <|> b) = (f <$> a) <|> (f <$> b)
--  OK     Left absorption (for fmap):  f <$> empty = empty
instance Monoid v => Alternative (Widget v) where
  empty = never
  f <|> g = orr [f,g]

instance Monoid v => MultiAlternative (Widget v) where
  orr = Widget . comb . map suspend
    where
      peelAllFree []           = Right []
      peelAllFree (Pure a : _) = Left a
      peelAllFree (Free s: fs) = fmap (s:) $ peelAllFree fs
      comb wfs = case peelAllFree wfs of
        Left a -> pure a
        Right fs -> Free $ Suspend (mconcat $ fmap view fs) (mconcat $ fmap runIO fs) (merge $ map cont fs)
        where
          merge ws = do
            (i, me) <- foldl (\prev (i,w) -> prev <|> fmap (i,) w) retry $ zip [0..] ws
            return $ fmap (\e -> comb $ take i wfs ++ [e] ++ drop (i+1) wfs) me

-- The default instance derives from Alternative
instance Monoid v => MonadPlus (Widget v)
