{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE CPP #-}
module Concur.Run where

import           Control.Monad          (void)
import           Control.Monad.Free     (Free (..))
import           Control.Monad.IO.Class (MonadIO (..))

import           GHCJS.DOM.Types        (JSM)
import           GHCJS.Foreign.QQ       (js, js_)
import           GHCJS.VDOM             (VNode, DOMNode, diff, mount, patch)
import qualified GHCJS.VDOM.Element     as E
-- import qualified GHCJS.VDOM.Event       as Ev

import GHCJS.DOM.Types (JSM)
import           GHCJS.Foreign.QQ
import           GHCJS.Types

import qualified GHCJS.VDOM.Component    as C
import qualified GHCJS.VDOM.DOMComponent as D
import qualified GHCJS.VDOM.Attribute    as A
import qualified GHCJS.VDOM.Element      as E
import qualified GHCJS.VDOM.Event        as Ev
import           GHCJS.VDOM
import           GHCJS.VDOM.QQ



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
type HTML = [VNode]

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
      let
        stepToWidget NoChange   = w'
        stepToWidget (Change a) = a
      case w' of
        Pure a -> return a
        Free ws -> do
          void $ diff mnt (E.div () $ view ws) >>= patch mnt
          case cont ws of
            Nothing -> Prelude.error "WARNING: Application exited: This is usually an error!"
            Just m  -> liftIO m >>= go mnt . stepToWidget
