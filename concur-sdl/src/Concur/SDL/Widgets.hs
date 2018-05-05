module Concur.SDL.Widgets where

import Control.Monad (when)
import Concur.Core (Widget, awaitViewAction, notify, display)
import Control.Concurrent.STM (atomically)
import Concur.SDL.Painter (Painter(Painter))
import SDL

-------------------------------------------------------------------------------
-- Event handlers
-- TODO: Wrap more events

-- Wait for a key to be pressed
keyboard :: Widget Painter Keycode
keyboard = awaitViewAction $ \n -> Painter $ \_ es -> mapM_ (keyEvent n) es
  where
    keyEvent n e = case eventPayload e of
      KeyboardEvent keyboardEvent ->
        when (keyboardEventKeyMotion keyboardEvent == Pressed)
          $ atomically $ notify n (keysymKeycode (keyboardEventKeysym keyboardEvent))
      _ -> pure ()

-------------------------------------------------------------------------------
-- Raw Drawing, with no event handling
--  (I'm lazy, so not wrapping all drawing primitives right now)
-- WARNING: the callback will be called repeatedly every frame!
--  Do not do anything else except check event status and draw to the renderer!
unsafeDraw :: (Renderer -> [Event] -> IO ()) -> Widget Painter a
unsafeDraw = display . Painter

unsafeDraw' :: (Renderer -> IO ()) -> Widget Painter a
unsafeDraw' f = display $ Painter $ const . f
