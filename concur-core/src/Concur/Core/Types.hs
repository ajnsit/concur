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
import           Control.Concurrent       (MVar, ThreadId, forkIO, killThread, newEmptyMVar, putMVar, takeMVar)
import           Control.Monad            (MonadPlus (..), forM)
import           Control.Monad.Free       (Free (..), hoistFree, liftF)
import           Control.Monad.IO.Class   (MonadIO, liftIO)
import           Control.MultiAlternative (MultiAlternative, orr, never)

import qualified Concur.Core.Notify       as N

data SuspendF v next
  = StepView v next
  | forall r. StepBlock (IO r) (r -> next)
  | forall r. StepIO    (IO r) (r -> next)
  | Forever

deriving instance Functor (SuspendF v)

newtype Widget v a = Widget { step :: Free (SuspendF v) a }
  deriving (Functor, Applicative, Monad)

view :: v -> Widget v ()
view v = Widget $ liftF $ StepView v ()

effect :: IO a -> Widget v a
effect a = Widget $ liftF $ StepBlock a id

io :: IO a ->  Widget v a
io a = Widget $ liftF $ StepIO a id

forever :: Widget v a
forever = Widget $ liftF Forever

continue :: SuspendF v a -> Widget v a
continue = Widget . liftF

display :: v -> Widget v a
display v = view v >> forever

-- Change the view of a Widget
mapView :: (u -> v) -> Widget u a -> Widget v a
mapView f (Widget w) = Widget $ go w
  where
    go = hoistFree g
    g (StepView v next)  = StepView (f v) next
    g (StepIO a next)    = StepIO a next
    g (StepBlock a next) = StepBlock a next
    g Forever            = Forever

-- Generic widget view wrapper
wrapView :: Applicative f => (u -> v) -> Widget u a -> Widget (f v) a
wrapView f = mapView (pure . f)

-- | IMPORTANT: Blocking IO is dangerous as it can block the entire UI from updating.
--   It should only be used for *very* quick running IO actions like creating MVars.
unsafeBlockingIO :: Monoid v => IO a -> Widget v a
unsafeBlockingIO = io

-- This is a safe use for blockingIO, and is exported
awaitViewAction :: (N.Notify a -> v) -> Widget v a
awaitViewAction f = do
  n <- io N.newNotify
  view (f n)
  effect $ N.await n

-- TODO: what to do when the parent dies?
loadWithIO :: IO a -> Widget v a
loadWithIO a = do
  n <- io $ do
    n <- newEmptyMVar
    _ <- forkIO $ a >>= putMVar n
    pure n
  effect $ takeMVar n

-- Make a Widget, which can be pushed to remotely
remoteWidget :: (MultiAlternative m, MonadUnsafeBlockingIO m, MonadSafeBlockingIO m, MonadIO m, Monad m, Show a) => m b -> (a -> m b) -> IO (a -> m (), m b)
remoteWidget d f = do
  var <- newEmptyMVar
  return (proxy var, wid var d)
  where
    proxy var = liftUnsafeBlockingIO . putMVar var
    wid var ui = orr [Left <$> ui, Right <$> liftSafeBlockingIO (takeMVar var)] >>= either return (wid var . f)

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

stepW :: v -> Free (SuspendF v) a -> IO (Either a (v, Maybe (IO (Free (SuspendF v) a))))
stepW _ (Free (StepView v next))  = stepW v next
stepW v (Free (StepIO a next))    = a >>= stepW v . next
stepW v (Free (StepBlock a next)) = pure $ Right (v, Just (a >>= pure . next))
stepW v (Free Forever)            = pure $ Right (v, Nothing)
stepW _ (Pure a)                  = pure $ Left a

instance Monoid v => MultiAlternative (Widget v) where
  never = display mempty

  -- Single child fast path without threads
  orr [w] = go (step w)
    where
      go widget = do
        stepped <- io $ stepW mempty widget

        case stepped of
          Left a                -> pure a
          Right (v, Nothing)    -> view v >> forever
          Right (v, Just await) -> do
            view v
            next <- effect await
            go next

  -- General threaded case
  orr ws = do
    mvar <- io newEmptyMVar
    comb mvar $ fmap (Left . step) ws
    where
      comb :: MVar (Int, Free (SuspendF v) a) -> [Either (Free (SuspendF v) a) (v, Maybe ThreadId)] -> Widget v a
      comb mvar widgets = do
        stepped <- io $ forM widgets $ \w -> case w of
          Left suspended         -> either Left (Right . Left) <$> stepW mempty suspended
          Right (displayed, tid) -> pure $ Right $ Right (displayed, tid)
  
        case sequence stepped of
          -- A widget finished, kill all running threads
          Left a -> do
            io $ sequence_
              [ killThread tid
              | Right (Right (_, Just tid)) <- stepped
              ]
            pure a
          Right next -> do
            -- Display all current views
            view $ mconcat $ map (either fst fst) next

            tids <- io $ forM (zip [0..] next) $ \(i, v) -> case v of
              -- Start a new thread on encountering StepBlock
              Left (dv, Just await) -> fmap (Right . (dv,) . Just) $ forkIO $ do
                a <- await
                putMVar mvar (i, a)

              -- Neverending Widget, pass on
              Left  (dv, Nothing)   -> pure $ Right (dv, Nothing)

              -- Already running, pass on
              Right (dv, tid)       -> pure $ Right (dv, tid)
                  
            (i, newWidget) <- effect $ takeMVar mvar
            comb mvar (take i tids ++ [Left newWidget] ++ drop (i + 1) tids)

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
