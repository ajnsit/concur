{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}
module Concur.Widgets where

import           Concur.Notify                 (Notify (..), newNotify)
import           Concur.Run                    (HTML)
import           Concur.Types                  (Widget, display, io, mapView,
                                                never)

import           Control.Applicative           ((<|>))
import           Control.Concurrent            (threadDelay)
import           Control.Monad.IO.Class        (MonadIO (..))

import qualified Data.JSString                 as JSS
import           GHCJS.DOM                     (currentDocumentUnchecked)
import           GHCJS.DOM.EventM              (mouseClientXY, on)
import           GHCJS.DOM.GlobalEventHandlers (click)
import           GHCJS.DOM.Types               (JSM)
import qualified GHCJS.VDOM.Attribute          as A
import qualified GHCJS.VDOM.Element            as E
import qualified GHCJS.VDOM.Event              as Ev

-- import           GHCJS.DOM.Document            (getBodyUnchecked)
-- import           GHCJS.DOM.Element             (setInnerHTML)
-- import           GHCJS.VDOM
-- import           GHCJS.VDOM.QQ


-- Notifications wrapper
withNotify :: (Notify a -> JSM b) -> JSM (Notify a)
withNotify f = do
  n <- liftIO newNotify
  _ <- f n
  return n

-- Global mouse click notifications
documentClickNotifications :: JSM (Notify (Int,Int))
documentClickNotifications = withNotify $ \n -> do
  doc <- currentDocumentUnchecked
  on doc click $ do
    (x, y) <- mouseClientXY
    liftIO $ notify n (x,y)

-- Text display widget
text :: String -> Widget HTML a
text s = display [E.text $ JSS.pack s]

-- Delay widget
delay :: Monoid v => Int -> Widget v ()
delay i = liftIO $ threadDelay (i*1000000)

-- A clickable button widget
button :: String -> Widget HTML ()
button s = do
  n <- liftIO newNotify
  let but = E.button (Ev.click (\_e -> notify n ())) [E.text $ JSS.pack s]
  io [but] $ await n

-- Text input. Returns the contents on keypress enter.
-- NOTE: This suffers from the usual virtual-dom lost focus problem :(
input :: String -> Widget HTML String
input def = do
  n <- liftIO newNotify
  let txt = E.input (A.value $ JSS.pack def, Ev.input (notify n . JSS.unpack . Ev.inputValue)) ()
  io [txt] $ await n

-- Append multiple widgets together
-- TODO: Make this more efficient
orr :: Monoid v => [Widget v a] -> Widget v a
orr = foldr (<|>) never

-- Package a widget inside a div
wrapDiv :: A.Attributes attrs => attrs -> Widget HTML a -> Widget HTML a
wrapDiv attrs = mapView (pure . E.div attrs)

-- Like wrapDiv but takes a list of widgets to match the usual Elm syntax
elDiv :: A.Attributes attrs => attrs -> [Widget HTML a] -> Widget HTML a
elDiv attrs = wrapDiv attrs . orr
