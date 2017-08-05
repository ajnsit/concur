{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE MultiWayIf        #-}
{-# LANGUAGE BangPatterns      #-}
module Main where

import           Control.Applicative    ((<|>))
import           Control.Monad          (forever, void)
import           Control.Monad.IO.Class (liftIO)
import           Control.Monad.State    (StateT, execStateT, get, lift, modify)

import           Data.Time.Clock
import qualified Data.JSString                 as JSS

import qualified GHCJS.VDOM.Attribute          as A
import qualified GHCJS.VDOM.Element            as E

import           Concur                 (HTML, Widget, button, delay,
                                         documentClickNotifications, initConcur,
                                         runWidgetInBody, text, wrapDiv, keyboardNotifications,
                                         interval, elT, el)

import Concur.Subscription.Window
import Concur.Subscription.Keyboard

data Mario = Mario
  { x :: !Double
  , y :: !Double
  , vx :: !Double
  , vy :: !Double
  , time :: !UTCTime
  , delta :: !Double
  , arrow :: !Arrows
  , dir :: !Dir
  , window :: !(Int,Int)
  }
data Dir = L | R deriving (Show, Eq)
type MarioWidget = StateT Mario (Widget HTML) ()

initMario :: UTCTime -> Mario
initMario now = Mario 0 0 0 0 now 0 (Arrows 0 0) R (0,0)

main :: IO ()
main = do
  -- This needs to be called once at the very beginning
  initConcur
  -- Run widget
  void $ runWidgetInBody mario

mario :: Widget HTML ()
mario = do
  now <- liftIO getCurrentTime
  void $ flip execStateT (initMario now) $ do
    -- Install an arrow key handler
    arrowKeys <- liftIO arrows
    -- Install a ticker that fires every 50 ms
    every50ms <- liftIO $ interval 50
    -- Install a listener for window resize events
    windowResizes <- liftIO windowResize
    -- Forever - draw mario, handle user input, and update physics
    forever $     (get >>= lift . drawMario)
              <|> (lift every50ms >>= modify . step)
              <|> (lift arrowKeys >>= modify . handleArrows)
              <|> (lift windowResizes >>= modify . resizeWindow)

handleArrows :: Arrows -> Mario -> Mario
handleArrows arrows m = m { arrow = arrows }

step :: UTCTime -> Mario -> Mario
step newTime m@Mario{..} =
  physics delta
  . jump arrow
  . walk arrow
  . gravity delta
  . updateTime newTime
  $ m
  where
    updateTime :: UTCTime -> Mario -> Mario
    updateTime newTime m@Mario{..} =
      m { delta = realToFrac $ newTime `diffUTCTime` time
        , time = newTime
        }

    gravity :: Double -> Mario -> Mario
    gravity dt m@Mario{..} =
      m { vy = if y > 0 then vy - dt*500 else 0 }

    walk :: Arrows -> Mario -> Mario
    walk Arrows{..} m@Mario{..} =
      m { vx = fromIntegral arrowX * 50
        , dir = if | arrowX < 0 -> L
                   | arrowX > 0 -> R
                   | otherwise -> dir
        }

    jump :: Arrows -> Mario -> Mario
    jump Arrows{..} m@Mario{..} =
        if arrowY > 0 && vy == 0
         then m { vy = 200 }
         else m

    physics :: Double -> Mario -> Mario
    physics dt m@Mario{..} =
      m { x = x + dt * vx
        , y = max 0 (y + dt * vy)
        }

resizeWindow :: (Int, Int) -> Mario -> Mario
resizeWindow dims m = m { window = dims }

drawMario :: Mario -> Widget HTML ()
drawMario m@Mario{..} = el E.div [ A.height h, A.width w ]
  [ el E.img
    [ A.height 37, A.width 37, A.src src, A.style marioStyle ]
    []
  ]
  where
    (w,h) = window
    verb = if | y > 0 -> "jump"
              | vx /= 0 -> "walk"
              | otherwise -> "stand"
    d = case dir of
      L -> "left"
      R -> "right"
    src = JSS.pack $ "../imgs/" ++ verb ++ "/" ++ d ++ ".gif"
    gy = 62 - (fromIntegral w / 2)
    marioStyle = JSS.pack $ "display:block; transform: " ++ matrix x (abs (y + gy))
    matrix x y = "matrix(1,0,0,1," ++ show x ++ "," ++ show y ++ ")"
