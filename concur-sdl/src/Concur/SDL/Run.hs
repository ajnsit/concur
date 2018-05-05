{-# LANGUAGE OverloadedStrings #-}
module Concur.SDL.Run where

import Control.Concurrent.STM (atomically)
import Control.Monad.Free (Free (..))
import Control.Monad.IO.Class (MonadIO (..))
import Data.Maybe (fromMaybe)

import Concur.Core
import Concur.SDL.Painter

import SDL

runWidget :: Widget Painter a -> IO a
runWidget (Widget w) = do
  initializeAll
  window <- createWindow "Concur SDL Application" defaultWindow
  renderer <- createRenderer window (-1) defaultRenderer
  appLoop renderer w

appLoop :: Renderer -> Free (Suspend Painter) a -> IO a
appLoop renderer w' = do
  events <- pollEvents
  case w' of
    Pure a -> pure a
    Free (Suspend io) -> io >>= \ws -> do
      let painter = view ws
      clear renderer
      paint painter renderer events
      present renderer
      liftIO (atomically $ fromMaybe (Free $ Suspend $ return ws) <$> cont ws) >>= appLoop renderer
