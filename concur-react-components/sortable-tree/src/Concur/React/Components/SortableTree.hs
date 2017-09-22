{-# LANGUAGE GHCForeignImportPrim #-}
{-# LANGUAGE MagicHash            #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE QuasiQuotes          #-}
module Concur.React.Components.SortableTree
  ( sortableTree
  , TreeData(..)
  )
where

import           Concur.Core                             (Widget, await, effect,
                                                          newNotify, notify)
import           Concur.React                            (HTML, getProp,
                                                          getPropObj, hasProp,
                                                          unDOMEvent, vattrData,
                                                          vevt, vleaf)

import           Control.Monad.STM                       (atomically)
import           Control.MonadSTM                        (MonadSTM (liftSTM))

import           System.IO.Unsafe                        (unsafePerformIO)
import           Unsafe.Coerce                           (unsafeCoerce)

import           JavaScript.Array                        (JSArray)
import qualified JavaScript.Array                        as JA

import           JavaScript.Object                       (Object)
import qualified JavaScript.Object                       as JO

import           GHCJS.Foreign.Internal                  (JSONType (..),
                                                          fromJSBool, toJSBool)
import qualified GHCJS.Foreign.Internal                  as GFI
import           GHCJS.Types                             (JSString, JSVal,
                                                          jsval)

import           Concur.React.Components.SortableTreeFFI (js_sortableTreeComponent)

-- State of a Sortable Tree.
data TreeData = TreeDataNode JSString Bool [TreeData] | TreeDataLeaf JSString
  deriving (Show, Eq)

-- A Sortable Tree. Returns the changed tree data.
sortableTree :: [TreeData] -> Widget HTML [TreeData]
sortableTree treeDataList = do
  n <- liftSTM newNotify
  let handler = \td -> unbakeTreeData (unDOMEvent td) >>= atomically . notify n
  let attrs = [vevt "onChange" handler, vattrData "treeData" $ jsval $ unsafeBakeTreeData treeDataList]
  effect [vleaf sortableTreeComponent attrs] $ await n

unsafeBakeTreeData :: [TreeData] -> JSArray
unsafeBakeTreeData ts = unsafePerformIO (bakeTreeData ts)
{-# INLINE unsafeBakeTreeData #-}

bakeTreeData :: [TreeData] -> IO JSArray
bakeTreeData ts = JA.fromList <$> mapM bakeTreeDataNode ts
  where
    bakeTreeDataNode (TreeDataLeaf title) = withJSObj $ JO.setProp "title" (jsval title)
    bakeTreeDataNode (TreeDataNode title expanded children) = withJSObj $ \o -> do
      JO.setProp "title" (jsval title) o
      JO.setProp "expanded" (toJSBool expanded) o
      c <- bakeTreeData children
      JO.setProp "children" (jsval c) o

withJSObj :: (Object -> IO ()) -> IO JSVal
withJSObj f = JO.create >>= \o -> f o >> return (jsval o)
{-# INLINE withJSObj #-}

unbakeTreeData :: JSVal -> IO [TreeData]
unbakeTreeData val =
  case GFI.jsonTypeOf val of
    JSONArray -> do
      let arr = unsafeCoerce val
      let children = JA.toList arr
      mapM unbakeTreeNode children
    _ -> return [errorLeaf]
  where
    errorLeaf = TreeDataLeaf "ERROR!: Invalid JSON data passed to SortableTree event handler"
    unbakeTreeNode v =
      if not (GFI.isObject v)
        then return errorLeaf
        else do
          if hasProp "children" v
            then do
              -- NOTE: Here it's okay to get props with raw ffi, instead of JO.getProp because
              -- we throw away the haskell ref to the object before it can be mutated by React.
              let title = getProp "title" v
              let childrenV = getPropObj "children" v
              children <- unbakeTreeData childrenV
              let expandedV = getPropObj "expanded" v
              let expanded = fromJSBool expandedV
              return $ TreeDataNode title expanded children
            else do
              let title = getProp "title" v
              return $ TreeDataLeaf title

sortableTreeComponent :: JSVal
sortableTreeComponent = js_sortableTreeComponent
{-# INLINE sortableTreeComponent #-}
