{-# LANGUAGE OverloadedStrings #-}
module Main where

import Control.Applicative ((<|>))

import Concur.Core
import Concur.React

-- Our possible actions
data CalculatorAction = Plus | Minus | Times | Div | Enter | Clear | Digit Int

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

-- Calc display
calcDisplay :: Int -> Widget HTML x
calcDisplay n = el "div" [] [text $ show n]

-- Hooking up everything is easy
main :: IO ()
main = runWidgetInBody $ go 0 []
  where
    go n s = do
      a <- calcDisplay n <|> calcButtonsWidget
      let (s', n') = calc s a in go n' s'
