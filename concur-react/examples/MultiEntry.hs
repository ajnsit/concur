{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
module Main where

import           Control.Monad        (forever, void)
import           Control.Monad.State  (execStateT, get, lift, modify)

import           Concur.Core
import           Concur.React

type MenuItems a = [(a,String)]

-- A Double menu, where the entries in the second menu depend on the first
doubleMenu :: String -> String -> MenuItems a -> (a -> MenuItems b) -> Widget HTML b
doubleMenu label1 label2 items f = menu1 >>= go
  where
    menu1 = menu label1 items
    menu2 a = menu label2 (f a)
    go a = orr [fmap Left menu1, fmap Right (menu2 a)] >>= either go return

-- A simple select menu
menu :: String -> MenuItems a -> Widget HTML a
menu label items = el_ "div" [vattr "className" "menu"] $ do
  button' [] (text label)
  orr $ map menuButton items
  where
    menuButton (ret,str) = ret <$ button' [] (text str)

data EntriesState = EntriesState { color :: String, entries :: [String] }
main :: IO ()
main = void $ runWidgetInBody $ flip execStateT (EntriesState "Red" []) $
  forever $ el "div" [vattr "className" "main"]
    [ lift $ el_ "h1" [] $ text "Select a color"
    , selColor
    , lift $ el_ "h1" [] $ text "Make entries"
    , newEntry
    , lift $ el_ "h1" [] $ text "Current entries"
    , entriesList
    ]
  where
    selColor = do
      c <- lift $ doubleMenu "Fruits" "Color" itemsFruit itemsColor
      modify $ \s -> s { color = c }
    newEntry = do
      EntriesState {..} <- get
      e <- lift $ menu ("New Entry for " ++ color ++ " fruit") $ itemsFruitColor color
      modify $ \s -> s { entries = e : entries }
    entriesList = do
      EntriesState {..} <- get
      lift $ orr $ map (el_ "div" [] . text) entries

-- Items for first menu
itemsFruit :: MenuItems String
itemsFruit =
  [ ("Apple","Apple")
  , ("Banana","Banana")
  ]

-- Items for second menu
itemsColor :: String -> MenuItems String
itemsColor "Apple" =
  [ ("Red","Red")
  , ("Green","Green")
  ]
itemsColor "Banana" =
  [ ("Yellow","Yellow")
  , ("Green","Green")
  ]
itemsColor _ = itemsColor "Apple"

-- Items for selecting fruit from color
itemsFruitColor :: String -> MenuItems String
itemsFruitColor "Red" =
  [ ("Apple","Apple")
  ]
itemsFruitColor "Green" =
  [ ("Apple","Apple")
  , ("Banana","Banana")
  ]
itemsFruitColor "Yellow" =
  [ ("Banana","Banana")
  ]
itemsFruitColor _ = itemsFruitColor "Red"
