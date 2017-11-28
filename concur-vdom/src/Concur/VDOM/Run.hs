{-# LANGUAGE CPP                      #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE QuasiQuotes              #-}
module Concur.VDOM.Run where

import           Control.Concurrent.STM (atomically)
import           Control.Monad          (void)
import           Control.Monad.Free     (Free (..))
import           Control.Monad.IO.Class (MonadIO (..))

import           Data.Maybe             (fromMaybe)

import           GHCJS.DOM.Types        (JSM)
import           GHCJS.Foreign.QQ       (js)
import           GHCJS.VDOM             (DOMNode, VNode, diff, mount, patch)
import qualified GHCJS.VDOM.Element     as E
import qualified GHCJS.VDOM.Event       as Ev

import           Concur.Core

-- HTML structure
type HTML = [VNode]
type HTMLNode = VNode
type HTMLWrapper = HTML -> HTMLNode
type HTMLNodeName attrs = attrs -> HTMLWrapper

initConcur :: JSM ()
initConcur = Ev.initEventDelegation Ev.defaultEvents

runWidgetInBody :: Widget HTML a -> JSM a
runWidgetInBody w = do
  root <- [js| document.body |]
  runWidget w root

runWidget :: Widget HTML a -> DOMNode -> JSM a
runWidget w root = runWidgetLoading w root (E.div () ())

runWidgetLoading :: Widget HTML a -> DOMNode -> HTMLNode -> JSM a
runWidgetLoading (Widget w) root loading = do
  m <- mount root loading
  go m w
  where
    go mnt w' = do
      case w' of
        Pure a -> liftIO (putStrLn "WARNING: Application exited: This may have been unintentional!") >> return a
        Free (Suspend io) -> liftIO io >>= \ws -> do
          void $ diff mnt (E.div () $ view ws) >>= patch mnt
          liftIO $ fromMaybe (return ()) $ runIO ws
          liftIO (atomically $ fromMaybe (Free $ Suspend $ return ws) <$> cont ws) >>= go mnt
