{-# LANGUAGE OverloadedStrings        #-}
{-# LANGUAGE FlexibleContexts         #-}
module Concur.React.Widgets where

import           GHCJS.Types                (JSString, JSVal)

import qualified Data.JSString              as JSS

import           Data.Void                  (Void, absurd)
import           Text.Read                  (readMaybe)

import           Control.Monad              (void, when)
import           Concur.Core
import           Control.Concurrent.STM     (STM, atomically)

import           Unsafe.Coerce              (unsafeCoerce)

import           Concur.React.DOM
import           Control.ShiftMap
import           Control.MonadSTM

-- TODO: Since we can't have a top level text in React. We currently always wrap it in span.
text :: String -> Widget HTML a
text txt = display [vtext $ JSS.pack txt]

-- Like el_ but accepts a React Component reference instead of a tagname
elComp :: (ShiftMap (Widget HTML) m) => JSVal -> [VAttr] -> m a -> m a
elComp e attrs = shiftMap (wrapView (vnode e attrs))

-- Generic Element wrapper (single child widget)
el_ :: (ShiftMap (Widget HTML) m) => JSString -> [VAttr] -> m a -> m a
el_ = elComp . unsafeCoerce

-- Generic Element wrapper
el :: (ShiftMap (Widget HTML) m, MultiAlternative m) => JSString -> [VAttr] -> [m a] -> m a
el e attrs = el_ e attrs . orr

-- Create a dom leaf node
elLeaf :: JSString -> [VAttr] -> Widget HTML a
elLeaf e attrs = display [vleaf (unsafeCoerce e) attrs]

-- Helper
mkEventHandlerAttr :: JSString -> STM (VAttr, STM JSVal)
mkEventHandlerAttr evtName = do
  -- TODO: Use blocking IO
  n <- newNotify
  let attr = VAttr evtName $ Right (atomically . notify n . unsafeCoerce)
  return (attr, await n)

-- Handle arbitrary events on an element.
elEvent :: (ShiftMap (Widget HTML) m, MultiAlternative m, Monad m, MonadSTM m)
        => JSString
        -> (JSVal -> a)
        -> JSString
        -> [VAttr]
        -> m a
        -> m a
elEvent evtName xtract tag attrs child = elEventComp evtName xtract (unsafeCoerce tag) attrs child

-- Like elEvent, but works for arbitrary react components
elEventComp :: (ShiftMap (Widget HTML) m, MultiAlternative m, Monad m, MonadSTM m)
        => JSString
        -> (JSVal -> a)
        -> JSVal
        -> [VAttr]
        -> m a
        -> m a
elEventComp evtName xtract e attrs child = do
  (a,w) <- liftSTM $ mkEventHandlerAttr evtName
  orr [fmap xtract $ liftSTM w, elComp e (a:attrs) child]

-- Similar to elEventComp, but specialised to the case where there are no child events.
elEventComp' :: (ShiftMap (Widget HTML) m, MultiAlternative m, Monad m, MonadSTM m)
         => JSString
         -> JSVal
         -> [VAttr]
         -> m Void
         -> m JSVal
elEventComp' evtName comp attrs child = elEventComp evtName id comp attrs (fmap absurd child)

-- Similar to elEvent, but specialised to the case where there are no child events.
elEvent' :: (ShiftMap (Widget HTML) m, MultiAlternative m, Monad m, MonadSTM m)
         => JSString
         -> JSString
         -> [VAttr]
         -> m Void
         -> m JSVal
elEvent' evtName tag attrs child = elEvent evtName id tag attrs (fmap absurd child)

-- A clickable button widget. Returns either the button click, or the child event.
button :: (ShiftMap (Widget HTML) m, MultiAlternative m, Monad m, MonadSTM m) => [VAttr] -> m () -> m ()
button attrs w = elEvent "onClick" (const ()) "button" attrs w

-- A clickable button widget, specialised to the case when there are no child events.
button' :: (ShiftMap (Widget HTML) m, MultiAlternative m, Monad m, MonadSTM m) => [VAttr] -> m Void -> m ()
button' attrs w = void $ elEvent' "onClick" "button" attrs w

-- Text input. Returns the contents on keypress enter.
inputEnter :: [VAttr] -> Widget HTML String
inputEnter = inputEnterVal ""

-- Text input. Returns the contents on keypress enter.
inputEnterVal :: String -> [VAttr] -> Widget HTML String
inputEnterVal curVal attrs = do
  n <- liftSTM newNotify
  let evtattr = vevt "onKeyDown" (handleKey n . unsafeCoerce)
  let valattr = vattr "defaultValue" (JSS.pack curVal)
  effect [vleaf (unsafeCoerce ("input" :: JSString)) (evtattr:valattr:attrs)] $ await n
  where
    handleKey n = \e -> do
      atomically $ when (getProp "key" e == "Enter") $ notify n $! JSS.unpack $ getProp "value" $ getPropObj "target" e

inputShowReadVal :: (Show a, Read a) => a -> Widget HTML a
inputShowReadVal n =
  readMaybe <$> inputEnterVal (show n) []
  >>= maybe (inputShowReadVal n) return
