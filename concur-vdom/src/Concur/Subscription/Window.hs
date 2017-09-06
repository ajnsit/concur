{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Concur.Subscription.Window
-- Copyright   :  (C) 2016-2017 David M. Johnson. Adapted by Anupam Jain.
-- License     :  BSD3-style (see the file LICENSE)
-- Maintainer  :  Anupam Jain
-- Stability   :  experimental
-- Portability :  non-portable
----------------------------------------------------------------------------
module Concur.Subscription.Window where

import           GHCJS.Foreign.Callback
import           GHCJS.Marshal

import           JavaScript.Object
import           JavaScript.Object.Internal

import           Control.Concurrent.STM     (STM, atomically)
import           Control.Monad.IO.Class     (MonadIO (liftIO))
import           Control.MonadSTM           (MonadSTM (liftSTM))

import           Concur.Core
import           Concur.VDOM.FFI

-- | Captures window coordinates changes as they occur
windowResize :: Monoid v => IO (Widget v (Int, Int))
windowResize = do
  n <- atomically newNotify
  liftIO $ do
    initSize <- (,) <$> windowInnerHeight <*> windowInnerWidth
    atomically $ notify n initSize
    windowAddEventListener "resize" =<< do
      asyncCallback1 $ \windowEvent -> do
        target <- getProp "target" (Object windowEvent)
        Just w <- fromJSVal =<< getProp "innerWidth" (Object target)
        Just h <- fromJSVal =<< getProp "innerHeight" (Object target)
        atomically $ notify n (h, w)
  return $ liftSTM $ await n
