{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
module Concur.React.DOM where

import           GHCJS.Foreign.Callback   (OnBlocked (..), syncCallback1)
import           GHCJS.Types              (JSString, JSVal, jsval)

import           JavaScript.Array         (JSArray)
import qualified JavaScript.Array         as JA

import           JavaScript.Object        (Object)
import qualified JavaScript.Object        as JO

import           Unsafe.Coerce            (unsafeCoerce)

import           Concur.Internal.ReactFFI

-- We build this pure Haskell representation, and then convert it to React DOM
type HTML = [VDOM]

data VDOM
  = VNode !JSVal ![VAttr] ![VDOM]
  | VLeaf !JSVal ![VAttr]
  | VText !JSString

data VAttr
  = VAttr
      { attrName  :: JSString
      , attrValue :: Either JSVal (DOMEvent -> IO ())
      }
  | VStyle
      { styleName  :: JSString
      , styleValue :: StyleVal
      }

-- React Style Attributes
data StyleVal = StyleString JSString | StyleVal JSVal

-- A Generic Event object.
-- TODO: Specialise to various types of events
newtype DOMEvent = DOMEvent { unDOMEvent :: JSVal }

-- Various constructors
vevt :: JSString -> (DOMEvent -> IO ()) -> VAttr
vevt name handler = VAttr name (Right handler)

vattr :: JSString -> JSString -> VAttr
vattr name val = VAttr name (Left $ unsafeCoerce val)

vattrData :: JSString -> JSVal -> VAttr
vattrData name val = VAttr name (Left val)

vnode :: JSVal -> [VAttr] -> [VDOM] -> VDOM
vnode = VNode

vleaf :: JSVal -> [VAttr] -> VDOM
vleaf = VLeaf

vtext :: JSString -> VDOM
vtext = VText

-- A JS Array of React nodes
newtype ReactHTML = ReactHTML { unReactHTML :: JSArray }

-- A React Node
newtype ReactNode = ReactNode {unReactNode :: JSVal }

-- An Actual browser DOM node
newtype DOMNode = DOMNode { unDOMNode :: JSVal }

-- JS Object with attributes
newtype ReactAttributes = ReactAttributes { unReactAttributes :: Object }

-- | Convert a list of vdom attributes to Attributes
bakeAttrs :: [VAttr] -> IO ReactAttributes
bakeAttrs attrs = do
  o <- JO.create
  s <- JO.create
  mapM_ (setAttr o s) attrs
  setStyle o s
  return $ ReactAttributes o
  where
    setAttr o _ (VAttr n (Left v)) = JO.setProp n v o
    setAttr o _ (VAttr n (Right h)) = do
      -- TODO: Handle retention of callbacks
      -- We need to use sync instead of async, otherwise react invalidates event objects
      -- https://facebook.github.io/react/docs/events.html#event-pooling
      cb <- syncCallback1 ThrowWouldBlock $ unsafeCoerce h
      JO.setProp n (jsval cb) o
    setAttr _ s (VStyle n (StyleString v)) = JO.setProp n (jsval v) s
    setAttr _ s (VStyle n (StyleVal v)) = JO.setProp n v s
    setStyle o s = JO.setProp "style" (jsval s) o

-- | Convert HTML to ReactHTML.
bakeReactHTML :: HTML -> IO ReactHTML
bakeReactHTML h = nodeToHTML <$> mapM go h
  where
    go (VNode tag attrs children) = mkReactParent tag <$> bakeAttrs attrs <*> bakeReactHTML children
    go (VLeaf tag attrs) = mkReactLeaf tag <$> bakeAttrs attrs
    go (VText str) = return $ mkText str
    nodeToHTML xs = ReactHTML $ JA.fromList $ unsafeCoerce xs

-- FFI Wrappers

-- Render a React App
renderReactDOM :: DOMNode -> ReactNode -> IO ()
renderReactDOM d v = js_renderReactDOM (unDOMNode d) (unReactNode v)
{-# INLINE renderReactDOM #-}

-- | PURE: Construct a react dom node with children.
mkReactParent :: JSVal -> ReactAttributes -> ReactHTML -> ReactNode
mkReactParent v a c = ReactNode $ js_mkReactParent v (unReactAttributes a) (unReactHTML c)
{-# INLINE mkReactParent #-}

-- | PURE: Construct a react dom node without children.
mkReactLeaf :: JSVal -> ReactAttributes -> ReactNode
mkReactLeaf v a = ReactNode $ js_mkReactLeaf v (unReactAttributes a)
{-# INLINE mkReactLeaf #-}

-- | PURE: Construct a text dom node.
mkText :: JSString -> ReactNode
mkText s = ReactNode $ js_mkText s
{-# INLINE mkText #-}

-- | Get the document body.
documentBody :: DOMNode
documentBody = DOMNode js_documentBody
{-# INLINE documentBody #-}

-- | Check if an object has a particular field
hasProp :: JSString -> JSVal -> Bool
hasProp = js_hasProp
{-# INLINE hasProp #-}

-- | Extract a String field from a JS object.
-- TODO: This is unsafe (if the field doesn't exist)
getProp :: JSString -> JSVal -> JSString
getProp = js_getProp
{-# INLINE getProp #-}

-- | Extract an object field from a JS object.
-- TODO: This is unsafe (if the field doesn't exist)
getPropObj :: JSString -> JSVal -> JSVal
getPropObj = js_getPropObj
{-# INLINE getPropObj #-}

-- | Create an detached dom element.
documentCreateElement :: JSString -> IO DOMNode
documentCreateElement s = DOMNode <$> js_documentCreateElement s
{-# INLINE documentCreateElement #-}

-- | Append an element to another.
appendChild :: DOMNode -> DOMNode -> IO ()
appendChild p c = js_appendChild (unDOMNode p) (unDOMNode c)
{-# INLINE appendChild #-}

-- | Print strings to the console.
consoleLog :: JSString -> IO ()
consoleLog = js_consoleLog
{-# INLINE consoleLog #-}

-- | Print objects to the console.
consoleLogObj :: JSVal -> IO ()
consoleLogObj = js_consoleLogObj
{-# INLINE consoleLogObj #-}


-- AJ: These two functions should be in ghcjs-prim

-- | Convert JS Val to Bool>
fromJSBool :: JSVal -> Bool
fromJSBool = js_fromJSBool
{-# INLINE fromJSBool #-}

-- | Convert Bool to JS Val.
toJSBool :: Bool -> JSVal
toJSBool = js_toJSBool
{-# INLINE toJSBool #-}
