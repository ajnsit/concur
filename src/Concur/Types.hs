{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TupleSections              #-}
module Concur.Types
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
  ) where

import           Concur.Notify          (newNotify, notify, await)
import           Control.Applicative    (Alternative, empty, (<|>))
import           Control.Concurrent     (forkIO)
import           Control.Concurrent.STM (STM, atomically)
import           Control.Monad          (MonadPlus (..), void)
import           Control.Monad.Free     (Free (..), hoistFree, liftF)
import           Control.Monad.IO.Class (MonadIO, liftIO)
import           Control.MonadSTM       (MonadSTM (..))

newtype Widget v a = Widget { suspend :: Free (Suspend v) a }
  deriving (Functor, Applicative, Monad)

data Suspend v a = Suspend { view :: v, runIO :: Maybe (IO ()), cont :: Effect a }
  deriving Functor

-- Nothing means no effects
type Effect a = Maybe (STM (Maybe a))

continue :: Suspend v a -> Widget v a
continue = Widget . liftF

widget :: v -> Effect a -> Widget v a
widget v r = continue $ Suspend v Nothing r

display :: v -> Widget v a
display v = widget v Nothing

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
effect v m = widget v $ Just $ Just <$> m

instance Monoid v => MonadSTM (Widget v) where
  liftSTM m = widget mempty $ Just $ Just <$> m

instance Monoid v => MonadIO (Widget v) where
  liftIO io = do
    n <- liftSTM newNotify
    continue $ Suspend mempty (Just $ void $ forkIO $ io >>= atomically . notify n) $ Just $ Just <$> (await n)

-- IMPORTANT NOTE: This Alternative instance is NOT the same one as that for Free.
-- That one simply uses Alternative for Suspend. But that one isn't sufficient for us.
instance Monoid v => Alternative (Widget v) where
  empty = never
  Widget f <|> Widget g = Widget $ comb f g
    where
      comb :: Monoid v => Free (Suspend v) a -> Free (Suspend v) a -> Free (Suspend v) a
      comb (Pure fa) _         = pure fa
      comb _         (Pure ga) = pure ga
      comb fss@(Free fs) gss@(Free gs) = Free $ Suspend (view fs `mappend` view gs) (mrunIO (runIO fs) (runIO gs)) $
        case (cont fs, cont gs) of
          (Nothing, Nothing) -> Nothing
          (Nothing, Just mg) -> Just $ fmap (comb fss) <$> mg
          (Just mf, Nothing) -> Just $ fmap (`comb` gss) <$> mf
          (Just mf, Just mg) -> Just $ do
            ev <- fmap Left mf <|> fmap Right mg
            return $ case ev of
              Left (Just m)  -> Just $ comb m gss
              Right (Just m) -> Just $ comb fss m
              _              -> Nothing
      mrunIO :: Maybe (IO ()) -> Maybe (IO ()) -> Maybe (IO ())
      mrunIO Nothing Nothing = Nothing
      mrunIO Nothing m = m
      mrunIO m Nothing = m
      mrunIO (Just m) (Just n) = Just $ m >> n

-- The default instance derives from Alternative
instance Monoid v => MonadPlus (Widget v)
