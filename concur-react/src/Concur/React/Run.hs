{-# LANGUAGE OverloadedStrings        #-}
module Concur.React.Run where

import           Control.Monad.Free     (Free (..))
import           Concur.Core
import           Concur.React.VDOM
import           Concur.React.FFI
import           Concur.React.Attributes
import           Data.Maybe             (fromMaybe)
import           Control.Monad.IO.Class (MonadIO (..))
import           Control.Concurrent.STM (atomically)

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
        Free ws -> do
          -- html <- bakeHTML $ view ws
          -- attrs <- bakeAttrs []
          html <- mkReactParent "div" <$> (bakeAttrs []) <*> (bakeHTML (view ws)) -- $ mkReactParent "div" (mkAttributes ()) $
          renderReactDOM root html
          liftIO $ fromMaybe (return ()) $ runIO ws
          liftIO (atomically $ fromMaybe w' <$> cont ws) >>= go
