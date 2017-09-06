{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE FlexibleContexts  #-}
module Concur.VDOM.Widgets where

import           Concur.Core
import           Concur.VDOM.Run               (HTML, HTMLNodeName)

import           Control.Applicative           (Alternative, empty, (<|>))
import           Control.Concurrent            (forkIO, threadDelay)
import           Control.Concurrent.STM        (STM, atomically)
import           Control.Monad                 (forever)
import           Control.Monad.IO.Class        (MonadIO (..))
import           Control.Monad.State           (execStateT, get, lift, put,
                                                when)
import           Control.MonadSTM              (MonadSTM (liftSTM))
import           Control.MonadShiftMap         (MonadShiftMap, shiftMap)

import           Data.List                     (intercalate)
import           Data.Maybe                    (mapMaybe)
import           Data.String                   (fromString)
import           Data.Time.Clock               (UTCTime, getCurrentTime)

import qualified Data.JSString                 as JSS
import           GHCJS.DOM                     (currentDocumentUnchecked)
import           GHCJS.DOM.EventM              (mouseClientXY, on, uiKeyCode)
import           GHCJS.DOM.GlobalEventHandlers (click, keyDown)
import qualified GHCJS.VDOM.Attribute          as A
import qualified GHCJS.VDOM.Element            as E
import qualified GHCJS.VDOM.Event              as Ev


-- Global mouse click notifications
-- Sets up the click handler once and then return a Widget that listens to it
documentClickNotifications :: Monoid v => IO (Widget v (Int,Int))
documentClickNotifications = do
  n <- atomically newNotify
  doc <- currentDocumentUnchecked
  _ <- on doc click $ do
    (x, y) <- mouseClientXY
    liftIO $ atomically $ notify n (x,y)
  return $ listenNotify n

-- Global Keyboard notifications
keyboardNotifications :: Monoid v => IO (Widget v Word)
keyboardNotifications = do
  n <- atomically newNotify
  doc <- currentDocumentUnchecked
  _ <- on doc keyDown $ do
    k <- uiKeyCode
    liftIO $ atomically $ notify n k
  return $ listenNotify n

-- Returns a widget which waits for a Notification to happen
listenNotify :: Monoid v => Notify a -> Widget v a
listenNotify = liftSTM . await

-- An example of a completely IO widget
-- Waits for the specified number of milliseconds
delay :: Monoid v => Int -> Widget v ()
delay i = liftIO $ threadDelay (i*1000)

interval :: Monoid v => Int -> IO (Widget v UTCTime)
interval i = do
  n <- atomically newNotify
  -- TODO: Kill Thread at some point. Use Weak TVars for it
  tid <- forkIO $ forever $ threadDelay (i*1000) >> getCurrentTime >>= atomically . notify n
  return $ listenNotify n

-- Text display widget
text :: String -> Widget HTML a
text s = display [E.text $ JSS.pack s]

-- A clickable button widget
button :: String -> Widget HTML ()
button s = clickEl E.button [] (const ()) [text s]

-- An Element which can be clicked
clickEl :: HTMLNodeName [A.Attribute] -> [A.Attribute] -> (Ev.MouseEvent -> a) -> [Widget HTML a] -> Widget HTML a
clickEl e attrs onClick children = either onClick id <$> elEvent Ev.click e attrs (orr children)

-- Handle arbitrary events on an element.
-- Returns Right on child events, and Left on event
elEvent :: ((a -> IO ()) -> A.Attribute)
        -> HTMLNodeName [A.Attribute]
        -> [A.Attribute]
        -> Widget HTML b
        -> Widget HTML (Either a b)
elEvent evt e attrs w = do
  n <- liftSTM newNotify
  let wEvt = listenNotify n
  let child = el_ e (evt (atomically . notify n): attrs) w
  fmap Left wEvt <|> fmap Right child

-- Text input. Returns the contents on keypress enter.
inputEnter :: [A.Attribute] -> Widget HTML String
inputEnter attrs = do
  n <- liftSTM newNotify
  let handleKeypress e = when (Ev.key e == "Enter") $ atomically $ notify n $ JSS.unpack $ Ev.inputValue e
  let txt = E.input (Ev.keydown handleKeypress : attrs) ()
  effect [txt] $ await n

-- Text input. Returns the contents on every change.
-- This allows setting the value of the textbox, however
--  it suffers from the usual virtual-dom lost focus problem :(
input :: String -> Widget HTML String
input def = do
  n <- liftSTM newNotify
  let txt = E.input (A.value $ JSS.pack def, Ev.input (atomically . notify n . JSS.unpack . Ev.inputValue)) ()
  effect [txt] $ await n

-- Text input. Returns the contents on keypress enter.
-- This one does not allow setting the value of the textbox, however
--  this does not suffer from the virtual-dom lost focus problem, as
--  the vdom representation of the textbox never changes
mkInput :: STM (Widget HTML String)
mkInput = do
  n <- newNotify
  let txt = E.input (Ev.input (atomically . notify n . JSS.unpack . Ev.inputValue)) ()
  return $ effect [txt] $ await n

-- A custom widget. An input field with a button.
-- When the button is pressed, the value of the input field is returned.
-- Note the use of local state to store the input value
inputWithButton :: String -> String -> Widget HTML String
inputWithButton label def = do
  inp <- liftSTM mkInput
  flip execStateT def $ go inp
  where
    -- On text change, we simply update the state, but on button press, we return the current state
    go inp= w inp >>= either (\s -> put s >> go inp) (const get)
    -- Note we put a space between the text and the button. `text` widget is polymorphic and can be inserted anywhere
    w inp = fmap Left (lift inp) <|> lift (text " ") <|> fmap Right (lift $ button label)

-- A Checkbox
checkbox :: Bool -> Widget HTML Bool
checkbox checked = do
  n <- liftSTM newNotify
  let chk = E.input (Ev.click (const $ atomically $ notify n (not checked))) ()
  effect [chk] $ await n

-- Generic Element wrapper (single child widget)
el_ :: MonadShiftMap (Widget HTML) m => HTMLNodeName [A.Attribute] -> [A.Attribute] -> m a -> m a
el_ e attrs = shiftMap (wrapView (e attrs))

-- Generic Element wrapper
el :: (MonadShiftMap (Widget HTML) m, MultiAlternative m) => HTMLNodeName [A.Attribute] -> [A.Attribute] -> [m a] -> m a
el e attrs = shiftMap (wrapView (e attrs)) . orr

-- Utility to easily create class attributes
classList :: [(String, Bool)] -> A.Attribute
classList xs = A.class_ $ fromString classes
  where classes = intercalate " " $ flip mapMaybe xs $ \(s,c) -> if c then Just s else Nothing
