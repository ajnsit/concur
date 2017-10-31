{-# LANGUAGE MultiWayIf        #-}
{-# LANGUAGE OverloadedStrings #-}
module Main where

import           Control.Applicative    ((<|>))
import           Control.Monad          (void)
import           Control.Monad.IO.Class (liftIO)

import           System.Random          as R

import qualified Data.Text.Lazy as T

import           Concur.Core            (Widget, display)
import           Concur.Brick
import qualified Concur.Brick.UI as UI

snake :: Widget View ()
snake = do
  text UI.red "Press enter to continue"
  <|> (liftIO (R.randomRIO (1,100)) >>= go)
  where
    go :: Int -> Widget View ()
    go n = do
      text UI.green "Here's a random number"
      text UI.red $ T.pack $ show n

main :: IO ()
main = do
  initConcur
  void $ runWidget snake
