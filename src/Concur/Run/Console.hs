module Concur.Run.Console where

import           Control.Monad.Free (Free (..))
import           Data.Maybe         (fromMaybe)

import           Concur
import           Concur.Concurrent  (await, newNotify, notify)

run :: Widget String a -> IO a
run (Widget w) = do
  case w of
    Pure a -> return a
    Free ws -> do
      n <- newNotify
      putStrLn $ view ws
      cont ws $ notify n
      mc <- await n
      run (Widget $ fromMaybe w mc)
