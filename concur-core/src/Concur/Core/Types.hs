{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TupleSections              #-}
module Concur.Core.Types
  ( Widget(..)
  , continue
  , display
  , mapView
  , wrapView
  , SuspendF(..)
  , awaitViewAction
  , MultiAlternative(..)
  , loadWithIO
  , remoteWidget
  , unsafeBlockingIO
  , MonadUnsafeBlockingIO(..)
  , MonadSafeBlockingIO(..)
  ) where

import           Control.Applicative      (Alternative, empty, (<|>))
import           Control.Concurrent       (MVar, ThreadId, forkIO, killThread, threadDelay, newEmptyMVar, putMVar, takeMVar)
import           Control.Monad            (MonadPlus (..), forM, forM_)
import           Control.Monad.Free       (Free (..), hoistFree, liftF)
import           Control.Monad.IO.Class   (MonadIO, liftIO)
import           Control.MultiAlternative (MultiAlternative, orr, never)

import           Concur.Core.Notify

data SuspendF v next
  = StepView v next
  | forall r. StepBlock (IO r) (r -> next)
  | forall r. StepIO    (IO r) (r -> next)

deriving instance Functor (SuspendF v)

newtype Widget v a = Widget { step :: Free (SuspendF v) a }
  deriving (Functor, Applicative, Monad)

view :: v -> Widget v ()
view v = Widget $ liftF $ StepView v ()

effect :: IO a -> Widget v a
effect a = Widget $ liftF $ StepBlock a id

io :: IO a ->  Widget v a
io a = Widget $ liftF $ StepIO a id

continue :: SuspendF v a -> Widget v a
continue = Widget . liftF

display :: v -> Widget v a
display v = do
  view v
  effect $ do
    threadDelay maxBound
    undefined

-- Change the view of a Widget
mapView :: (u -> v) -> Widget u a -> Widget v a
mapView f (Widget w) = Widget $ go w
  where
    go = hoistFree g
    g (StepView v next)  = StepView (f v) next
    g (StepIO a next)    = StepIO a next
    g (StepBlock a next) = StepBlock a next

-- Generic widget view wrapper
wrapView :: Applicative f => (u -> v) -> Widget u a -> Widget (f v) a
wrapView f = mapView (pure . f)

-- | IMPORTANT: Blocking IO is dangerous as it can block the entire UI from updating.
--   It should only be used for *very* quick running IO actions like creating MVars.
unsafeBlockingIO :: Monoid v => IO a -> Widget v a
unsafeBlockingIO = io

-- This is a safe use for blockingIO, and is exported
awaitViewAction :: (Notify a -> v) -> Widget v a
awaitViewAction f = do
  n <- io newNotify
  view (f n)
  effect $ await n

-- TODO: what to do when the parent dies?
loadWithIO :: IO a -> Widget v a
loadWithIO a = do
  n <- io $ do
    n <- newEmptyMVar
    _ <- forkIO $ a >>= putMVar n
    pure n
  effect $ takeMVar n

-- Make a Widget, which can be pushed to remotely
remoteWidget :: (MultiAlternative m, MonadUnsafeBlockingIO m, MonadSafeBlockingIO m, Monad m) => m b -> (a -> m b) -> IO (a -> m (), m b)
remoteWidget d f = do
  var <- newNotify
  return (proxy var, wid var d)
  where
    proxy var = \a -> liftUnsafeBlockingIO $ notify var a
    wid var ui = orr [Left <$> ui, Right <$> (liftSafeBlockingIO $ await var)] >>= either return (wid var . f)

instance Monoid v => MonadIO (Widget v) where
  liftIO = loadWithIO

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
  never = display mempty
  orr ws = do
    mvar <- io newEmptyMVar
    comb mvar $ fmap (Left . step) ws
    where
      go :: v -> Free (SuspendF v) a -> IO (Either a (v, IO (Free (SuspendF v) a)))
      go _ (Free (StepView v next))  = go v next
      go v (Free (StepIO a next))    = a >>= go v . next
      go v (Free (StepBlock a next)) = pure $ Right (v, a >>= pure . next)
      go _ (Pure a)                  = pure $ Left a
  
      comb :: MVar (Int, Free (SuspendF v) a) -> [Either (Free (SuspendF v) a) (v, ThreadId)] -> Widget v a
      comb mvar vs = do
        rs <- io $ forM vs $ \v -> case v of
          Left w -> do
            r <- go mempty w
            pure $ case r of
              Left a -> Left a
              Right b -> Right $ Left b
          Right (w, tid) -> pure $ Right $ Right (w, tid)
  
        case traverse id rs of
          Left a -> do
            io $ forM_ rs $ \r -> case r of
              Right (Right (_, tid)) -> killThread tid
              _ -> pure ()
            pure a
          Right xs -> do
            view $ mconcat $ flip map xs $ \x -> case x of
              Left  (v, _) -> v
              Right (v, _) -> v
            tids <- io $ do
              forM (zip [0..] xs) $ \(i, v) -> case v of
                Left (w, ioa) -> fmap (Right . (w,)) $ forkIO $ do
                  a <- ioa
                  putMVar mvar (i, a)
                Right (w, tid) -> pure $ Right (w, tid)
                  
            (i, me) <- effect $ takeMVar mvar
            comb mvar (take i tids ++ [Left me] ++ drop (i+1) tids)

-- The default instance derives from Alternative
instance Monoid v => MonadPlus (Widget v)

class MonadUnsafeBlockingIO m where
  liftUnsafeBlockingIO :: IO a -> m a

instance MonadUnsafeBlockingIO (Widget v) where
  liftUnsafeBlockingIO = io

class MonadSafeBlockingIO m where
  liftSafeBlockingIO :: IO a -> m a

instance MonadSafeBlockingIO (Widget v) where
  liftSafeBlockingIO = effect
