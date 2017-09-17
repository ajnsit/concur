{-# LANGUAGE GHCForeignImportPrim #-}
{-# LANGUAGE MagicHash            #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE QuasiQuotes          #-}
module Main where

import           Control.Monad              (forever)
import           Control.Monad.STM          (atomically)
import           Control.MonadSTM           (MonadSTM (liftSTM))

import           Concur.Core
import           Concur.React

import           Unsafe.Coerce              (unsafeCoerce)

import           GHCJS.Foreign.QQ           (js')
import           GHCJS.Prim                 (toJSInt)
import           GHCJS.Types                (JSString, JSVal)

import qualified Data.JSString              as JSS

import           Concur.React.Attributes    (Attribute (Attribute))

import qualified GHCJS.Prim.Internal.Build  as IB
import qualified JavaScript.Object.Internal as OI

import           Concur.React.Components.SortableTree (TreeData (..), sortableTree)

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
