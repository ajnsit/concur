{-# LANGUAGE OverloadedStrings #-}
module Main where

import           Control.Applicative    ((<|>))
import           Control.Monad          (forever, void)
import           Control.Monad.IO.Class (liftIO)
import           Control.Monad.State    (execStateT, get, lift, modify, put)

import qualified GHCJS.VDOM.Attribute   as A

import           Concur                 (HTML, Notify, Widget, await, button,
                                         documentClickNotifications, elDiv,
                                         initConcur, input, runWidgetInBody,
                                         text, wrapDiv)

-- Simple TODO List
todos :: Widget HTML ()
todos = void $ wrapDiv (A.class_ "todos") $ flip execStateT [] $ forever $ add <|> list
  where
    add = do
      l <- get
      s <- lift $ wrapDiv (A.class_ "add") $ inputWithButton "Add" ""
      put (s:l)
    list = do
      l <- get
      lift $ elDiv (A.class_ "list") $ map renderTodo l
    renderTodo s = wrapDiv (A.class_ "todo") $ text s

-- A custom widget. An input field with a button.
-- When the button is pressed, the value of the input field is returned.
-- Note the use of local state to store the input value
-- NOTE: This currently suffers from the usual virtual-dom lost input focus problem :(
inputWithButton :: String -> String -> Widget HTML String
inputWithButton label def = flip execStateT def go
  where
    -- On text change, we simply update the state, but on button press, we return the current state
    go = w >>= either (\s -> put s >> go) (const get)
    -- Note we put a space between the text and the button. `text` widget is polymorphic and can be inserted anywhere
    w = fmap Left (get >>= lift . input) <|> lift (text " ") <|> fmap Right (lift $ button label)

main :: IO ()
main = do
  -- This needs to be called once at the very beginning
  initConcur
  -- Run widget
  runWidgetInBody todos
