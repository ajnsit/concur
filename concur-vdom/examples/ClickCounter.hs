{-# LANGUAGE OverloadedStrings #-}
module Main where

import           Control.Applicative    ((<|>))
import           Control.Monad          (forever, void)
import           Control.Monad.IO.Class (liftIO)
import           Control.Monad.State    (execStateT, get, lift, modify)

import qualified GHCJS.VDOM.Element     as E

import           Concur.Core            (Widget)
import           Concur.VDOM            (HTML, button, delay,
                                         documentClickNotifications, el_,
                                         initConcur, runWidgetInBody, text)

-- Click counter widget
-- This widget is stateful, it maintains the current number of clicks
-- We can simply use the StateT monad transformer
clickCounter :: Widget HTML ()
clickCounter = void $ flip execStateT (0::Int) $ do
    -- Setup a global click handler once
    docClicks <- liftIO $ documentClickNotifications
    -- Run forever - processing clicks AND displaying count
    forever $ autoIncrement <|> increment10 <|> handleClicks docClicks <|> displayCount
  where
    -- Automatically increment clicks every second. Note the simple synchronous control flow.
    autoIncrement = lift (delay 1000) >> modify (+1)
    -- Increment clicks by 10 when a button is pressed. Note that this also counts as a click on the document, so it's actually incremented by 11.
    increment10 = lift (el_ E.div [] $ button "Increment by 10") >> modify (+10)
    -- Await document click event, increment click count on each click anywhere in the page.
    handleClicks docClicks = lift docClicks >> modify (+1)
    -- Get click count, and display it using `text` widget
    displayCount = get >>= \count -> lift $ el_ E.div [] $ text $ show count ++ " clicks"

main :: IO ()
main = do
  -- This needs to be called once at the very beginning
  initConcur
  -- Run widget
  void $ runWidgetInBody clickCounter
