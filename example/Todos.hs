{-# LANGUAGE ForeignFunctionInterface #-}
module Main where

import           Control.Applicative    ((<|>))
import           Control.Concurrent     (threadDelay)
import           Control.Monad          (void)
import           Control.Monad.IO.Class (liftIO)
import           Control.Monad.State

import           Concur
import           Concur.Run.Console (run)

example :: Widget String ()
example = do
  display "Waiting for 1 second" <|> do
    delay 1
    display " Done..." <|> delay 0
  display "Complete" <|> delay 0

todos :: Widget String [String]
todos = do
  flip execStateT [] $ forever $ add <|> list
  where
    add = do
      liftIO $ putStr "Add> "
      s <- liftIO getLine
      l <- get
      put (s:l)
    list = do
      l <- get
      lift (display (show l))

-- Sample widgets
delay :: Int -> Widget String ()
delay i = liftIO $ threadDelay (i*1000000)

main :: IO ()
main = void $ run todos
