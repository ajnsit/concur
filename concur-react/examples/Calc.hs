{-# LANGUAGE OverloadedStrings #-}
module Main where

import Control.MonadSTM

import Concur.Core
import Concur.React

-- Possible actions emited by the Calculator buttons
data CalculatorAction = Plus | Minus | Times | Div | Enter | Clear | Digit Int
  deriving Show

-- Button pad widget
calcButtonsWidget :: Widget HTML CalculatorAction
calcButtonsWidget = el "div" []
  [ el "div" [] [d 7, d 8, d 9, opDiv]
  , el "div" [] [d 4, d 5, d 6, opTimes]
  , el "div" [] [d 1, d 2, d 3, opMinus]
  , el "div" [] [d 0, ent, cls, opPlus]
  ]
  where
    d n     = but (Digit n) (show n)
    ent     = but Enter "⏎"
    cls     = but Clear "C"
    opDiv   = but Div "/"
    opTimes = but Times "*"
    opMinus = but Minus "-"
    opPlus = but Plus "+"
    but x s = (const x) <$> button [] (text s)

-- Postfix calculation
calc :: [Int] -> CalculatorAction -> ([Int], Int)
calc (n:s)   (Digit d) = new (n*10+d) s
calc s       (Digit d) = new d s
calc _       Clear     = ([],0)
calc s       Enter     = (0:s,0)
calc (y:x:s) Plus      = new (x+y) s
calc (y:x:s) Minus     = new (x-y) s
calc (y:x:s) Times     = new (x*y) s
calc (y:x:s) Div       = new (x `div` y) s
calc s       _         = (s,0)
new :: Int -> [Int] -> ([Int], Int)
new n s = (n:s, n)

-- Hooking up everything is pretty easy as can be seen in `mainStandard`
mainStandard :: IO ()
mainStandard = runWidgetInBody $ go 0 []
  where
    go n s = do
      a <- orr [text (show n), calcButtonsWidget]
      let (s', n') = calc s a in go n' s'

-- But in this example we don't use this "standard" way of doing things

-- Instead, we show off remote widgets to drive the display
-- This code may seem longer, but it's sometimes much cleaner to use "action at a distance".
-- It's also very useful to avoid having to rework complex logic.

-- We first create a widget that handles wiring up the buttons and calculation
-- Notice the extremely straightforward flow.
-- We also don't need to worry WHERE and HOW the result is displayed
buttonsWidget :: (Int -> Widget HTML ()) -> Widget HTML y
buttonsWidget showResultWidget = go []
  where
    -- This Widget effectively -
    go st = do
      -- 1. Displays the calculator buttons
      a <- calcButtonsWidget
      -- 2. Updates the state of the calculation when a button is pressed
      let (st', n) = calc st a
      -- 3. Uses the widget passed in to display the current result
      showResultWidget n
      -- 4. Repeats
      go st'

-- Create a remote calculator display which can be controlled by other widgets
makeCalcDisplay :: Widget HTML (Int -> Widget HTML (), Widget HTML x)
makeCalcDisplay = liftSTM $ remoteWidget defaultDisplay handleResult
  where
    defaultDisplay = text "This display is controlled by other widgets. GO AHEAD. PRESS A BUTTON."
    handleResult res = text $ show res

-- Now we wire them together easily
main :: IO ()
main = runWidgetInBody $ do
  (showResult, calcDisp) <- makeCalcDisplay
  el "div" [] [calcDisp, buttonsWidget showResult]
