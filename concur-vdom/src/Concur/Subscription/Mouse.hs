{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Concur.Subscription.Mouse
-- Copyright   :  (C) 2016-2017 David M. Johnson. Adapted by Anupam Jain.
-- License     :  BSD3-style (see the file LICENSE)
-- Maintainer  :  Anupam Jain
-- Stability   :  experimental
-- Portability :  non-portable
----------------------------------------------------------------------------
module Concur.Subscription.Mouse (mouseMove) where

import           GHCJS.Foreign.Callback
import           GHCJS.Marshal

import           JavaScript.Object
import           JavaScript.Object.Internal

import           Control.Concurrent.STM     (STM, atomically)
import           Control.Monad.IO.Class     (MonadIO (liftIO))
import           Control.MonadSTM           (MonadSTM (liftSTM))

import           Concur.Core
import           Concur.VDOM.FFI

-- | Captures mouse coordinates as they occur and writes them to
-- an event sink
mouseMove :: (Monad m, Monoid v) => IO (Widget v m (Int,Int))
mouseMove = do
  n <- newNotifyIO
  windowAddEventListener "mousemove" =<< do
    asyncCallback1 $ \mouseEvent -> do
      Just x <- fromJSVal =<< getProp "clientX" (Object mouseEvent)
      Just y <- fromJSVal =<< getProp "clientY" (Object mouseEvent)
      atomically $ notify n (x,y)
  return $ liftSTM $ await n
