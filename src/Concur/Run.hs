{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE CPP #-}
module Concur.Run where

import           Control.Monad          (void)
import           Control.Monad.Free     (Free (..))
import           Control.Monad.IO.Class (MonadIO (..))
import           Control.Concurrent.STM (atomically, retry)

import           GHCJS.DOM.Types        (JSM)
import           GHCJS.Foreign.QQ       (js)
import           GHCJS.VDOM             (VNode, DOMNode, diff, mount, patch)
import qualified GHCJS.VDOM.Element     as E
import qualified GHCJS.VDOM.Event       as Ev

import           Concur.Types

#if defined(ghcjs_HOST_OS)
run :: a -> a
run = id
#elif defined(MIN_VERSION_jsaddle_wkwebview)
import Language.Javascript.JSaddle.WKWebView (run)
#else
import Language.Javascript.JSaddle.WebKitGTK (run)
#endif


-- HTML structure
type HTML = [HTMLNode]
type HTMLNode = VNode
type HTMLNodeName attrs = attrs -> HTML -> HTMLNode

initConcur :: JSM ()
initConcur = Ev.initEventDelegation Ev.defaultEvents

runWidgetInBody :: Widget HTML a -> JSM a
runWidgetInBody w = do
  root <- [js| document.body |]
  runWidget w root

runWidget :: Widget HTML a -> DOMNode -> JSM a
runWidget (Widget w) root = do
  m <- mount root (E.div () ())
  go m w
  where
    go mnt w' = do
      case w' of
        Pure a -> liftIO (putStrLn "WARNING: Application exited: This may have been unintentional!") >> return a
        Free ws -> do
          void $ diff mnt (E.div () $ view ws) >>= patch mnt
          case cont ws of
            Nothing -> Prelude.error "ERROR: Application suspended indefinitely: This is usually a logic error!"
            Just m  ->
              let m' = atomically $ do
                    v <- m
                    case v of
                      Retry -> retry
                      NoChange -> return w'
                      Change a -> return a
              in liftIO m' >>= go mnt
