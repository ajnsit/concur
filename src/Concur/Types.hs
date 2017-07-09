{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TupleSections              #-}
module Concur.Types
  ( Widget(..)
  , widget
  , display
  , Suspend
  , view
  , cont
  , Effect
  ) where

import           Control.Applicative    (Alternative, empty, (<|>))
import           Control.Concurrent     (forkIO)
import           Control.Monad          (MonadPlus (..), void)
import           Control.Monad.Free     (Free (..), liftF)
import           Control.Monad.IO.Class (MonadIO, liftIO)

import           Concur.Concurrent      (await, newNotify, notify)
import           Concur.Free            (combineFree)

-------------
-- WIDGETS --
-------------

newtype Widget v a = Widget { unWidget :: Free (Suspend v) a }
  deriving (Functor, Applicative, Monad)

data Suspend v a = Suspend { view :: v, cont :: Effect a }
  deriving Functor

type Effect a = (Maybe a -> IO ()) -> IO ()

widget :: v -> Effect a -> Widget v a
widget v r = Widget $ liftF $ Suspend v r

display :: v -> Widget v a
display v = widget v $ const $ pure ()

effect :: Monoid v => ((Maybe a -> IO ()) -> IO ()) -> Widget v a
effect = widget mempty

instance Monoid v => Alternative (Widget v) where
  empty = display mempty
  Widget f <|> Widget g = Widget $ combineFree retmL retmR combLR f g
    where
      retmL fa _ = pure fa
      retmR _ ga = pure ga
      combLR fs gs = Free $ Suspend (view fs `mappend` view gs) (mergeEffect (cont fs) (cont gs))
      mergeEffect fas gas ret = void $ forkIO $ do
        n <- newNotify
        _ <- fas $ notify n . (True,)
        _ <- gas $ notify n . (False,)
        res <- await n
        ret $ case res of
          (_, Nothing)     -> Nothing
          (True, Just f')  -> Just $ unWidget $ Widget f' <|> Widget g
          (False, Just g') -> Just $ unWidget $ Widget f <|> Widget g'

-- The default instance derives from Alternative
instance Monoid v => MonadPlus (Widget v)

instance Monoid v => MonadIO (Widget v) where
  liftIO io = effect $ \ret -> io >>= ret . Just
