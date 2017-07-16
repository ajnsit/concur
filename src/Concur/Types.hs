{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TupleSections              #-}
module Concur.Types
  ( Widget(..)
  , continue
  , widget
  , display
  , pass
  , retry
  , Suspend
  , view
  , cont
  , Effect
  , io
  , effect
  , Step(..)
  ) where

import           Control.Applicative    (Alternative, empty, (<|>))
import           Control.Concurrent     (forkIO, killThread)
import           Control.Monad          (MonadPlus (..))
import           Control.Monad.Free     (Free (..), liftF)
import           Control.Monad.IO.Class (MonadIO, liftIO)

import           Concur.Notify          (await, newNotify, notify)

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
type Effect a = Maybe (IO (Step a))

data Step a
  = NoChange
--  | Err String
  | Change a
  deriving Functor

continue :: Suspend v a -> Widget v a
continue = Widget . liftF

widget :: v -> Effect a -> Widget v a
widget v r = continue $ Suspend v r

display :: v -> Widget v a
display v = widget v Nothing

-- This is probably useful for realtime systems only (i.e. not DOM, but maybe so for terminal)
-- This is like `return`, but is delayed by 1 cycle (i.e. is a Free instead of a Pure), so it doesn't immediately override anything else <|> with it, and allows things <|> with it to display their views (albeit momentarily)
pass :: Monoid v => a -> Widget v a
pass a = effect $ Just $ return $ Change a

-- This is probably useful for realtime systems only (i.e. not DOM, but maybe so for terminal)
-- <|> with this immediately restarts the entire computation
retry :: Monoid v => Widget v a
retry = effect $ Just $ return NoChange

io :: v -> IO a -> Widget v a
io v m = widget v $ Just $ Change <$> m

effect :: Monoid v => Effect a -> Widget v a
effect = widget mempty

-- IMPORTANT NOTE: This Alternative instance is NOT the same one as that for Free.
-- That one simply uses Alternative for Suspend. But that one isn't sufficient for us.
instance Monoid v => Alternative (Widget v) where
  empty = display mempty
  Widget f <|> Widget g = Widget $ comb f g
    where
      comb :: Monoid v => Free (Suspend v) a -> Free (Suspend v) a -> Free (Suspend v) a
      comb (Pure fa) _         = pure fa
      comb _         (Pure ga) = pure ga
      comb fss@(Free fs) gss@(Free gs) = Free $ Suspend (view fs `mappend` view gs) $
        case (cont fs, cont gs) of
          (Nothing, Nothing) -> Nothing
          (Nothing, Just iog) -> Just $ fmap (comb fss) <$> iog
          (Just iof, Nothing) -> Just $ fmap (`comb` gss) <$> iof
          (Just iof, Just iog) -> Just $ do
            n <- newNotify
            ft <- forkIO $ iof >>= notify n . (True,)
            gt <- forkIO $ iog >>= notify n . (False,)
            res <- await n
            -- This indiscriminate culling is probably a bad thing
            killThread ft
            killThread gt
            -- end massacre
            return $ case res of
              (_, NoChange)      -> NoChange
              (True, Change f')  -> Change $ comb f' gss
              (False, Change g') -> Change $ comb fss g'

-- The default instance derives from Alternative
instance Monoid v => MonadPlus (Widget v)

instance Monoid v => MonadIO (Widget v) where
  liftIO = io mempty
