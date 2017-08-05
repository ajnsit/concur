{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE OverloadedStrings   #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Concur.Subscription.Keyboard
-- Copyright   :  (C) 2016-2017 David M. Johnson. Adapted by Anupam Jain.
-- License     :  BSD3-style (see the file LICENSE)
-- Maintainer  :  Anupam Jain
-- Stability   :  experimental
-- Portability :  non-portable
----------------------------------------------------------------------------
module Concur.Subscription.Keyboard
  ( -- * Types
    Arrows (..)
    -- * Subscriptions
  , arrows
  , keyboard
  ) where

import           Data.IORef
import           Data.Set (Set)
import qualified Data.Set as S
import           GHCJS.Foreign.Callback
import           GHCJS.Marshal
import           JavaScript.Object
import           JavaScript.Object.Internal

import Control.Concurrent.STM (STM, atomically, newTVar, readTVar, writeTVar)
import Control.MonadSTM (MonadSTM (liftSTM))
import Control.Monad.IO.Class (MonadIO (liftIO))

import Concur.FFI
import Concur.Types
import Concur.Notify

-- | type for arrow keys currently pressed
--  37 left arrow  ( x = -1 )
--  38 up arrow    ( y =  1 )
--  39 right arrow ( x =  1 )
--  40 down arrow  ( y = -1 )
data Arrows = Arrows {
   arrowX :: !Int
 , arrowY :: !Int
 } deriving (Show, Eq)

-- | Helper function to convert keys currently pressed to `Arrow`
toArrows :: Set Int -> Arrows
toArrows set =
  Arrows {
    arrowX =
      case (S.member 37 set, S.member 39 set) of
        (True, False) -> -1
        (False, True) -> 1
        (_,_) -> 0
 ,  arrowY =
      case (S.member 40 set, S.member 38 set) of
        (True, False) -> -1
        (False, True) -> 1
        (_,_) -> 0
 }

keyboard :: Monoid v => IO (Widget v (Set Int))
keyboard = do
  n <- atomically newNotify
  kset <- atomically $ newTVar (S.empty)
  windowAddEventListener "keyup" =<< keyUpCallback n kset
  windowAddEventListener "keydown" =<< keyDownCallback n kset
  return $ liftSTM $ await n
  where
    keyDownCallback n kset = do
      asyncCallback1 $ \keyDownEvent -> do
        Just key <- fromJSVal =<< getProp "keyCode" (Object keyDownEvent)
        atomically $ do
          keys <- readTVar kset
          let newKeys = S.insert key keys
          writeTVar kset newKeys
          notify n newKeys
    keyUpCallback n kset = do
      asyncCallback1 $ \keyUpEvent -> do
        Just key <- fromJSVal =<< getProp "keyCode" (Object keyUpEvent)
        atomically $ do
          keys <- readTVar kset
          let newKeys = S.delete key keys
          writeTVar kset newKeys
          notify n newKeys

-- | Maps `Arrows` onto a Keyboard subscription
arrows :: Monoid v => IO (Widget v Arrows)
arrows = fmap toArrows <$> keyboard
