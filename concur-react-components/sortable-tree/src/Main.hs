{-# LANGUAGE OverloadedStrings    #-}
module Main where

import           Concur.React                         (ReactStyle (..), el, el_,
                                                       reactStyle,
                                                       runWidgetInBody, text)
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
    parentStyle = reactStyle
      [("display", StyleString "flex")
      ,("height", StyleString "800px")
      ]
    childStyle = reactStyle [("width", StyleString "50%")]
    showTree items = do
      modifiedItems <- el "div" [parentStyle]
        [ el_ "div" [childStyle] $ sortableTree items
        , el_ "div" [childStyle] $ text $ show items
        ]
      showTree modifiedItems
