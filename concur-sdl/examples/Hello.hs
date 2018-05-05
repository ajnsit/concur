{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TupleSections     #-}
module Main where

import Control.Applicative    ((<|>))
import Concur.Core
import Concur.SDL
import SDL

-- Very simple hello world
-- For each key press, add a rectangle to the screen

keysWidget :: Widget Painter ()
keysWidget = go [] 0
  where
    dispRects rects = unsafeDraw' $ \r -> mapM_ (dispRect r) rects
    dispRect renderer rect = fillRect renderer (Just rect)
    newRect xpos = Rectangle (P (V2 xpos 0)) (pure 5)
    go rects xpos = do
      k <- keyboard <|> dispRects rects
      if k == KeycodeQ
        then pure ()
        else go (newRect xpos: rects) (xpos + 10)

main :: IO ()
main = runWidget keysWidget
