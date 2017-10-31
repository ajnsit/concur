{-# LANGUAGE OverloadedStrings #-}
module Concur.Brick.Run where

import           Control.Concurrent.STM (atomically)
import           Control.Monad          (void)
import           Control.Monad.Free     (Free (..))
import           Control.Monad.IO.Class (MonadIO (..))

import           Data.Maybe             (fromMaybe)

import           Concur.Core
import           qualified Concur.Brick.UI as UI

import           Graphics.Vty           (Vty (nextEvent, update), mkVty, userConfig, text, shutdown, horizCat, Image, picForImage, defAttr, withForeColor, red)

-- TODO: This won't take care of background and cursor
-- We don't use the existing Monoid instance for Images
type View = [Image]

initConcur :: IO ()
initConcur = return ()

runWidget :: Widget View a -> IO a
runWidget w = runWidgetLoading w [text (defAttr `withForeColor` red) "Loading....."]

runWidgetLoading :: Widget View a -> View -> IO a
runWidgetLoading (Widget w) loading = do
  -- Load a configuration from getAppUserDataDirectory/config and $VTY_CONFIG_FILE.
  conf <- userConfig
  vty <- mkVty conf
  -- Show loading
  render vty loading
  go vty w
  where
    go vty w' = do
      case w' of
        Pure a -> shutdown vty >> return a
        Free (Suspend io) -> io >>= \ws -> do
          render vty (view ws)
          fromMaybe (return ()) $ runIO ws
          e <- nextEvent vty
          return () -- TODO: handleEvent e
          (atomically $ fromMaybe w' <$> cont ws) >>= go vty
    render vty images = update vty $ picForImage $ horizCat images
