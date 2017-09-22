{-# LANGUAGE OverloadedStrings #-}
module Main where

import           Concur.React                         (el, el_, runWidgetInBody,
                                                       text, vstyleStr)
import           Concur.React.Components.SortableTree (TreeData (..),
                                                       sortableTree)

main :: IO ()
main = runWidgetInBody $
         showTree [ TreeDataNode "Fruits" False
                      [ TreeDataLeaf "Apple"
                      , TreeDataLeaf "Banana"
                      ]
                  , TreeDataNode "Veggies" False
                      [ TreeDataLeaf "Tomato"
                      , TreeDataLeaf "Potato"
                      ]
                  , TreeDataNode "Colors" False
                      [ TreeDataLeaf "Red"
                      , TreeDataLeaf "Green"
                      , TreeDataLeaf "Blue"
                      , TreeDataLeaf "White"
                      , TreeDataLeaf "Orange"
                      ]
                  ]
  where
    parentStyle =
      [ vstyleStr "display" "flex"
      , vstyleStr "height" "800px"
      ]
    childStyle = [vstyleStr "width" "50%"]
    showTree items = do
      modifiedItems <- el "div" parentStyle
        [ el_ "div" childStyle $ sortableTree items
        , el_ "div" childStyle $ text $ show items
        ]
      showTree modifiedItems
