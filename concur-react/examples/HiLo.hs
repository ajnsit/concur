{-# LANGUAGE MultiWayIf        #-}
{-# LANGUAGE OverloadedStrings #-}
module Main where

import           Control.Applicative    ((<|>))
import           Control.Monad          (forever)
import           Control.Monad.IO.Class (liftIO)

import           System.Random          as R
import           Text.Read              (readMaybe)

import           Concur.Core
import           Concur.React

-- Hi/Lo Game. Demonstrates simple architecture of a Concur app.
-- Also a good demonstration of how Concur makes IO effects safe at widget transitions (the random number generation).
main :: IO ()
main = runWidgetInBody $ forever $ do
  el_ "h1" [] (text "I'm thinking of a number between 1 and 100")
  <|> (liftIO (R.randomRIO (1,100)) >>= go)
  where
    go :: Int -> Widget HTML ()
    go n = do
      guessStr <- el "div" []
        [ text "Try to guess: "
        , inputEnter [vattr "autoFocus" ""] -- [Attribute "autofocus" ""]
        ]
      case readMaybe guessStr of
        Nothing -> go n
        Just guess -> do
          if | guess <  n -> el_ "div" [] (text $ show guess ++ " - Go High!") <|> go n
             | guess >  n -> el_ "div" [] (text $ show guess ++ " - Go Low!") <|> go n
             | otherwise  -> el_ "div" [] (text $ "You guessed it! The answer was " ++ show n)
                 <|> (button [] (text "Play again"))
