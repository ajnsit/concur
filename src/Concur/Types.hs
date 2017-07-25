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
  , pass
  , restart
  , Suspend
  , view
  , cont
  , Effect
  , effect
  , Step(..)
  ) where

import           Control.Applicative    (Alternative, empty, (<|>))
import           Control.Concurrent.STM (STM)
import           Control.Monad          (MonadPlus (..))
import           Control.Monad.Free     (Free (..), hoistFree, liftF)
import           Control.MonadSTM       (MonadSTM (..))

-------------
-- WIDGETS --
-------------

newtype Widget v a = Widget { suspend :: Free (Suspend v) a }
  deriving (Functor, Applicative, Monad)

data Suspend v a = Suspend { view :: v, cont :: Effect a }
  deriving Functor

-- Nothing means no effects
--   This is an error at the top level,
--   and must be <|> with another widget to be useful
type Effect a = Maybe (STM (Step a))

data Step a
  = Retry
  | NoChange
--  | Err String
  | Change a
  deriving Functor

continue :: Suspend v a -> Widget v a
continue = Widget . liftF

widget :: v -> Effect a -> Widget v a
widget v r = continue $ Suspend v r

display :: v -> Widget v a
display v = widget v Nothing

-- Never returns, use as an identity for <|>
never :: Monoid v => Widget v a
never = display mempty

-- Change the view of a Widget
mapView :: (u -> v) -> Widget u a -> Widget v a
mapView f (Widget w) = Widget $ go w
  where
    go = hoistFree $ \s -> Suspend (f $ view s) (cont s)

-- Generic widget view wrapper
wrapView :: Applicative f => (u -> v) -> Widget u a -> Widget (f v) a
wrapView f = mapView (pure . f)

-- This is probably useful for realtime systems only (i.e. not DOM, but maybe so for terminal)
-- This is like `return`, but is delayed by 1 cycle (i.e. is a Free instead of a Pure), so it doesn't immediately override anything else <|> with it, and allows things <|> with it to display their views (albeit momentarily)
pass :: Monoid v => a -> Widget v a
pass a = widget mempty $ Just $ return $ Change a

-- This is probably useful for realtime systems only (i.e. not DOM, but maybe so for terminal)
-- <|> with this immediately restarts the entire computation
restart :: Monoid v => Widget v a
restart = widget mempty $ Just $ return NoChange

effect :: v -> STM (Maybe a) -> Widget v a
effect v m = widget v $ Just $ do
  val <- m
  case val of
    Nothing -> return Retry
    Just a  -> return $ Change a

-- IMPORTANT NOTE: Be careful with this! If this blocks, it can break the rest of the app.
-- TODO: Perhaps hide this from the user code.
instance Monoid v => MonadSTM (Widget v) where
  liftSTM m = widget mempty $ Just $ Change <$> m

-- IMPORTANT NOTE: This Alternative instance is NOT the same one as that for Free.
-- That one simply uses Alternative for Suspend. But that one isn't sufficient for us.
instance Monoid v => Alternative (Widget v) where
  empty = never
  Widget f <|> Widget g = Widget $ comb f g
    where
      comb :: Monoid v => Free (Suspend v) a -> Free (Suspend v) a -> Free (Suspend v) a
      comb (Pure fa) _         = pure fa
      comb _         (Pure ga) = pure ga
      comb fss@(Free fs) gss@(Free gs) = Free $ Suspend (view fs `mappend` view gs) $
        case (cont fs, cont gs) of
          (Nothing, Nothing) -> Nothing
          (Nothing, Just mg) -> Just $ fmap (comb fss) <$> mg
          (Just mf, Nothing) -> Just $ fmap (`comb` gss) <$> mf
          (Just mf, Just mg) -> Just $ do
            -- It's very important that mf NOT block
            vf <- mf
            case vf of
              NoChange -> return NoChange
              Change f' -> return $ Change $ comb f' gss
              Retry -> do
                vg <- mg
                case vg of
                  NoChange  -> return NoChange
                  Change g' -> return $ Change $ comb fss g'
                  Retry     -> return Retry

-- The default instance derives from Alternative
instance Monoid v => MonadPlus (Widget v)
