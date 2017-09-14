{-# LANGUAGE OverloadedStrings #-}
module Main where

import           Control.Monad (forever)

import           Concur.Core
import           Concur.React

-- Demonstration of how easy it is to build a simple generic menu widget
-- 1. This uses no state, as it was easy to build this using monadic flow
-- 2. It was built by composing sub-widgets in a style that feels very functional.
--    Top, open, menuItem, and menuButton are legitimate widgets on their own.
menu :: [(String, [(a,String)])] -> Widget HTML a
menu cs = top 0 items >>= open items
  where
    items = menuItem <$> cs
    top i opts = orr $ zipWith (\(a,b) j -> a >>= \v -> return (b v,j)) opts [i..]
    open opts (b,i) =
      let w = [Left <$> top 0 (take i opts), Right <$> b, Left <$> top (i+1) (drop (i+1) opts)]
      in orr w >>= either (open opts) return
    menuItem (label, children) =
      ( el_ "div" [vattr "className" "menu"] $ button' [] (text label)
      , const $ el_ "div" [vattr "className" "menu"] $ orr $ map menuButton children
      )
    menuButton (ret,str) = ret <$ button' [] (text str)

main :: IO ()
main = runWidgetInBody $ forever $ do
  v <- menu items
  el "div" [] $ [text $ "You picked - " ++ v, button' [] $ text "Restart"]
  where
    items =
        [ ("Fruits",
            [ ("Apple","Apple")
            , ("Banana","Banana")
            ]
          )
        , ("Veggies",
            [ ("Tomato","Tomato")
            , ("Potato","Potato")
            ]
          )
        , ("Colors",
            [ ("Red","Red")
            , ("Green","Green")
            , ("Blue","Blue")
            , ("White","White")
            , ("Orange","Orange")
            ]
          )
        ]
