{-# LANGUAGE OverloadedStrings #-}
module Concur.React.Run where

import           Concur.Core            (Suspend (..), SuspendF (..),
                                         Widget (..))
import           Concur.React.DOM       (DOMNode, HTML, bakeAttrs,
                                         bakeReactHTML, documentBody,
                                         mkReactParent, renderReactDOM)

import           Control.Concurrent.STM (atomically)
import           Control.Monad.Free     (Free (..))
import           Control.Monad.IO.Class (MonadIO (..))

import           Data.Maybe             (fromMaybe)
import           GHCJS.Types            (JSString)
import           Unsafe.Coerce          (unsafeCoerce)

runWidgetInBody :: Widget HTML a -> IO a
runWidgetInBody w = do
  let root = documentBody
  runWidget w root

runWidget :: Widget HTML a -> DOMNode -> IO a
runWidget (Widget w) root = go w
  where
    go :: Free (Suspend HTML) a -> IO a
    go w' = do
      case w' of
        Pure a -> liftIO (putStrLn "WARNING: Application exited: This may have been unintentional!") >> return a
        Free (Suspend io) -> liftIO io >>= \ws -> do
          html <- mkReactParent (unsafeCoerce ("div" :: JSString)) <$> (bakeAttrs []) <*> (bakeReactHTML (view ws))
          renderReactDOM root html
          liftIO $ fromMaybe (return ()) $ runIO ws
          liftIO (atomically $ fromMaybe w' <$> cont ws) >>= go
