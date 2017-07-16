module Main where

import           Control.Applicative    ((<|>))
import           Control.Monad          (forever, void)
import           Control.Monad.IO.Class (liftIO)
import           Control.Monad.State    (execStateT, get, lift, modify)

import           Concur                 (HTML, Notify, Widget, await, button,
                                         documentClickNotifications, initConcur,
                                         runWidgetInBody, text)

-- Click counter widget
-- This widget is stateful, it maintains the current number of clicks
-- We can simply use the StateT monad transformer
clickCounter :: Notify click -> Widget HTML ()
clickCounter clicks = void $ flip execStateT (0::Int) $
    -- Run forever - processing clicks AND displaying count
    forever $ handleClicks <|> increment10 <|> displayCount
  where
    -- Increment clicks by 10. Note the simple synchronous control flow.
    increment10 = lift (button "Increment by 10") >> modify (+10)
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
    (clickCounter clicks)
      <|>
    (text " clicks")
