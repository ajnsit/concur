{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
module Main where

import           Control.Monad        (forever, void)
import           Control.Monad.State  (StateT, execStateT, get, lift, modify,
                                       put)

import           Data.Bool            (bool)
import           Data.IntMap          (IntMap)
import qualified Data.IntMap          as IntMap
import           Data.Maybe           (fromMaybe, isJust)

import           Text.Read            (readMaybe)

import qualified GHCJS.VDOM.Attribute as A
import qualified GHCJS.VDOM.Element   as E

import           Concur               (HTML, Widget, clickEl, el, el_,
                                       initConcur, inputEnter, orr,
                                       runWidgetInBody, text)

main :: IO ()
main = do
  -- This needs to be called once at the very beginning
  initConcur
  -- Run widget
  runWidgetInBody $ void $ flip execStateT IntMap.empty startRun

---------------------
-- Data Structures --
---------------------
type GameRun = (Int, RunStats) -- Last known time (in centiseconds) + RunStats
type RunStats = IntMap Int -- Boss (Int 1..10) -> Time (in centiseconds) taken for that boss

addBossRun :: Int -> Int -> GameRun -> GameRun
addBossRun b t (tprev, im) = (t, IntMap.insert b (t - tprev) im)

finishAndCommitGameRun :: GameRun -> RunStats -> RunStats
finishAndCommitGameRun (_, gs) = IntMap.unionWith min gs

-------------
-- Widgets --
-------------

-- Main menu options
-- Note that we don't need a global action type (as we would have to in elm)
data MainMenu = StartRun | ResetData | Quit

-- The main widget. We use StateT to hold game stats.
-- Note that the global state doesn't need to track either of the following (which would be required in Elm) -
--   1. Our current place in the menu system
--   2. The sub state of intermediate boss times. We localise that state when we need it.
startRun :: StateT RunStats (Widget HTML) a
startRun = el_ E.table [] $ el_ E.tr [] $ forever $ do
  -- Current Game stats + Intial menu
  opt <- orr
    [ get >>= lift . flip displayStats Nothing
    , el_ E.td [] $ lift $ menu
      [ (StartRun, "Start Run")
      , (ResetData, "Reset Data")
      , (Quit, "Quit")
      ]
    ]
  case opt of
    Quit -> lift $ text "Application exited..."
    ResetData -> put IntMap.empty
    StartRun -> do
      -- Start recording a run. Shows extended game stats + Run menu
      s <- get
      -- During a single run, the global stats don't change.
      -- So we switch to a localised sub state which records only the data for a game run
      gr <- lift $ flip execStateT (0, IntMap.empty) $ runWhile $ orr
        [ get >>= lift . displayStats s . Just . snd
        , el_ E.td [] enterRunTimeMenu
        ]
      modify $ finishAndCommitGameRun gr

-- Current Run Menu Options
data RunMenu = EnterTime | CancelRun | DiscardRun

-- Widget to Enter Boss Times for a complete Game Run
-- This widget returns
--    False - if the run is finished (we have entered time for all bosses, or the user picked cancel)
--    True  - The run is not finished (there are bosses left), and this widget needs to be called again to finish.
enterRunTimeMenu :: StateT GameRun (Widget HTML) Bool
enterRunTimeMenu = do
  opt <- lift $ menu
    [ (EnterTime, "Enter Time")
    , (CancelRun, "Cancel Run (& save new bests)")
    , (DiscardRun, "Quit Run (& undo bests)")
    ]
  case opt of
    CancelRun -> return False
    DiscardRun -> put (0, IntMap.empty) >> return False
    EnterTime -> do
      (_, gr) <- get
      let remainingBosses = filter (\i -> not $ isJust $ IntMap.lookup i gr) [1..10]
      case remainingBosses of
        [] -> return False
        (x:xs) -> do
          b <- if null xs || x > 6
                 then return x
                 else lift $ menu $ map (\i -> (i, "Boss " ++ show i)) $ filter (<= 6) remainingBosses
          mt <- lift $ orr
            [ el_ E.div [] $ text $ "Entering time for: Boss " ++ show b
            , el_ E.div [] $ Just <$> timeEntry
            , menuButton Nothing "Cancel"
            ]
          case mt of
            Nothing -> return True
            Just t -> do
              modify $ addBossRun b t
              return (not $ null xs)

-- Widget to Display Stats in the left pane.
-- If a GameRun is supplied, it shows an extra column to show the delta from the previous best timing.
displayStats :: RunStats -> Maybe RunStats -> Widget HTML a
displayStats s mrs = el_ E.td [] $ do
  el E.table [] $
    map renderBoss [1..6]
    ++ [el_ E.tr [] $ el_ E.td [] $ el E.hr [] []]
    ++ map renderBoss [7..10]
    ++ [el_ E.tr [] $ el_ E.td [] $ el E.hr [] []]
    ++ [el E.tr []
         [ el_ E.td [] $ text "Sum of best:"
         , el_ E.td [] $ text $ formatTime False $ sum $ IntMap.elems s
         ]
       ]
  where
    renderBoss i = el E.tr []
      [ el_ E.td [] $ text $ "Boss " ++ show i
      , el_ E.td [] $ text $ maybe "(none)" (formatTime False) $ IntMap.lookup i s
      , el_ E.td [] $ text $ maybe "" (maybe "(none)" (formatTime True) . (\rs -> (\x -> x - fromMaybe 0 (IntMap.lookup i s)) <$> IntMap.lookup i rs)) mrs
      ]

-- A Time entry widget. Returns time in centi-seconds.
timeEntry :: Widget HTML Int
timeEntry = orr
  [ el_ E.div [] $ text "XXX:YY:ZZ, where XXX is minutes, YY is seconds, and ZZ is hundreths of a second"
  , el_ E.div [] $ runWhileMaybe $ fmap readTimeMaybe $ inputEnter [A.type_ "text", A.maxlength 9]
  ]
  where
    readTimeMaybe str = getTime <$> readMaybe h <*> readMaybe s <*> readMaybe c
      where
        (h,r)  = break (== ':') str
        (s,r') = break (== ':') (safeTail r)
        c      = safeTail r'
    safeTail r = case r of [] -> ""; (_:xs) -> xs
    getTime m s c = m * 60 * 100 + s * 100 + c

-- Format time in centiseconds for display
formatTime :: Bool -> Int -> String
formatTime showPlus t
  | t < 0 = "-" ++ formatTime False (negate t)
  | showPlus && t > 0 = "+" ++ formatTime False t
  | otherwise = show m ++ ":" ++ show s ++ ":" ++ show c
  where
    (s', c) = t `divMod` 100
    (m, s) = s' `divMod` 60

-- A Menu widget
menu :: [(a,String)] -> Widget HTML a
menu = orr . map (uncurry menuButton)

-- Button that returns a specific value on click
menuButton :: a -> String -> Widget HTML a
menuButton ret str = el_ E.div [] $ clickEl E.button [A.class_ "menubutton"] (const ret) [text str]

-- Execute an action repeatedly until it returns False
runWhile :: Monad m => m Bool -> m ()
runWhile m = let go = m >>= bool (return ()) go in go

-- Execute an action repeatedly until it returns a value
runWhileMaybe :: Monad m => m (Maybe a) -> m a
runWhileMaybe m = let go = m >>= maybe go return in go
