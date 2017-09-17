{-# LANGUAGE GHCForeignImportPrim #-}
{-# LANGUAGE MagicHash            #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE QuasiQuotes          #-}
module Concur.React.Components.SortableTree
  ( sortableTree
  , TreeData(..)
  )
where

import           Concur.Core               (Widget, await, effect, newNotify,
                                            notify)
import           Concur.React              (HTML, vattrData, vevt, vleaf)
import           Concur.React.FFI          (fromJSBool, hasProp, toJSBool)

import           Control.Monad.STM         (atomically)
import           Control.MonadSTM          (MonadSTM (liftSTM))

import           Unsafe.Coerce             (unsafeCoerce)

import           GHCJS.Prim                (fromJSArray, getProp)
import qualified GHCJS.Prim.Internal.Build as IB
import           GHCJS.Types               (JSString, JSVal)

-- State of a Sortable Tree.
data TreeData = TreeDataNode JSString Bool [TreeData] | TreeDataLeaf JSString
  deriving (Show, Eq)

-- A Sortable Tree. Returns the changed tree data.
sortableTree :: [TreeData] -> Widget HTML [TreeData]
sortableTree treeDataList = do
  n <- liftSTM newNotify
  let handler = \td -> unbakeTreeData (unsafeCoerce td) >>= atomically . notify n
  let attrs = [vevt "onChange" handler, vattrData "treeData" $ bakeTreeData treeDataList]
  effect [vleaf sortableTreeComponent attrs] $ await n

bakeTreeData :: [TreeData] -> JSVal
bakeTreeData ts = IB.buildArrayI (map bakeTreeDataNode ts)
  where
    bakeTreeDataNode (TreeDataLeaf title) = IB.buildObjectI
      [ (unsafeCoerce ("title"::JSString), unsafeCoerce title) ]
    bakeTreeDataNode (TreeDataNode title expanded children) = IB.buildObjectI
      [ (unsafeCoerce ("title"::JSString), unsafeCoerce title)
      , (unsafeCoerce ("expanded"::JSString), toJSBool expanded)
      , (unsafeCoerce ("children"::JSString), bakeTreeData children)
      ]

unbakeTreeData :: JSVal -> IO [TreeData]
unbakeTreeData val = do
  children <- fromJSArray val
  mapM unbakeTreeNode children
  where
    unbakeTreeNode v
      | hasProp "children" v = do
          titleV <- getProp v "title"
          let title = unsafeCoerce titleV
          childrenV <- getProp v "children"
          children <- unbakeTreeData childrenV
          expandedV <- getProp v "expanded"
          let expanded = fromJSBool expandedV
          return $ TreeDataNode title expanded children
      | otherwise = do
          titleV <- getProp v "title"
          let title = unsafeCoerce titleV
          return $ TreeDataLeaf title

-- | PURE: Access to the SortableTree component
foreign import javascript unsafe "h$ffi.SortableTree"
  sortableTreeComponent :: JSVal
