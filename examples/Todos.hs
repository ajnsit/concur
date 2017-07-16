module Main where

import           Control.Applicative    ((<|>))
import           Control.Monad          (forever, void)
import           Control.Monad.IO.Class (liftIO)
import           Control.Monad.State    (execStateT, get, lift, modify)

import           Concur                 (HTML, Notify, Widget, await,
                                         documentClickNotifications, initConcur,
                                         runWidgetInBody, text)

data TodoAction
  = TodoAdd String
  | TodoRemove Int

-- todos :: Widget HTML ()
-- todos = void $ flip execStateT [] $
--   forever $ do
--     action <- add <|> list
--     a
--   where
--     add = do
--       liftIO $ putStr "Add> "
--       s <- liftIO getLine
--       l <- get
--       put (s:l)
--     list = do
--       l <- get
--       lift (display (show l))

-- Sample widgets

-- Click counter widget
-- This widget is stateful, it maintains the current number of clicks
-- We can simply use the StateT monad transformer
clickCounter :: Notify click -> Widget HTML ()
clickCounter clicks = void $ flip execStateT (0::Int) $
    -- Run forever - processing clicks AND displaying count
    forever $ handleClicks <|> displayCount
  where
    -- Await click event in IO monad, increment click count
    handleClicks = liftIO (await clicks) >> modify (+1)
    -- Get click count, and display it using `text` widget
    displayCount = get >>= lift . text . show

main :: IO ()
main = do
  -- This needs to be called once at the very beginning
  initConcur
  -- Setup global event handlers once
  clicks <- documentClickNotifications
  -- Run widget
  void $ runWidgetInBody $
    (text "You clicked ")
      <|>
    (clickCounter clicks)
      <|>
    (text " times")
