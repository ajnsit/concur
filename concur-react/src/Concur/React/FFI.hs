module Concur.React.FFI where

import           GHCJS.Foreign.Callback    (Callback (..), OnBlocked (..),
                                            syncCallback1)
import qualified GHCJS.Prim.Internal.Build as IB
import           GHCJS.Types               (JSString, JSVal, jsval)
import           Unsafe.Coerce             (unsafeCoerce)

import           Concur.React.VDOM         (HTML, VAttr (..), VDOM (..))

-- A JS Array of React nodes
newtype HTML' = HTML' JSVal

-- A React Node
newtype ReactNode = ReactNode JSVal

-- An Actual browser DOM node
newtype DOMNode = DOMNode JSVal

-- | Convert a list of React Nodes to HTML'.
bakeHTML' :: [ReactNode] -> HTML'
bakeHTML' xs = HTML' $ IB.buildArrayI $ unsafeCoerce xs

-- JS Object with attributes
newtype ReactAttributes = ReactAttributes JSVal

-- | Convert a list of vdom attributes to Attributes
bakeAttrs :: [VAttr] -> IO ReactAttributes
bakeAttrs attrs = do
  xs <- mapM mkAttr attrs
  return $ mkAttrs xs
  where
    mkAttr (VAttr n (Left v)) = return (unsafeCoerce n, v)
    mkAttr (VAttr n (Right h)) = do
      -- TODO: Handle retention of callbacks
      -- We need to use sync instead of async, otherwise react invalidates event objects
      -- https://facebook.github.io/react/docs/events.html#event-pooling
      cb <- syncCallback1 ThrowWouldBlock $ unsafeCoerce h
      return (unsafeCoerce n, jsval cb)
    mkAttrs xs = ReactAttributes $ IB.buildObjectI xs

-- | Convert HTML to HTML'.
bakeHTML :: HTML -> IO HTML'
bakeHTML h = bakeHTML' <$> mapM go h
  where
    go (VNode tag attrs children) = mkReactParent tag <$> bakeAttrs attrs <*> bakeHTML children
    go (VLeaf tag attrs) = mkReactLeaf tag <$> bakeAttrs attrs
    go (VText str) = return $ mkText str

-- | Perform an action at the next animation frame.
foreign import javascript unsafe "window.requestAnimationFrame($1)"
  requestAnimationFrame :: Callback (IO ()) -> IO ()

-- Render a React App
foreign import javascript unsafe "h$concur.ReactDOM.render($2, $1)"
  renderReactDOM :: DOMNode -> ReactNode -> IO ()

-- | PURE: Construct a react dom node with children.
foreign import javascript unsafe "h$concur.React.createElement($1, $2, $3)"
  mkReactParent :: JSVal -> ReactAttributes -> HTML' -> ReactNode

-- | PURE: Construct a react dom node without children.
foreign import javascript unsafe "h$concur.React.createElement($1, $2)"
  mkReactLeaf :: JSVal -> ReactAttributes -> ReactNode

-- | PURE: Construct a text dom node.
foreign import javascript unsafe "$r = $1;"
  mkText :: JSString -> ReactNode

-- | Prevent the default event action from taking place.
-- foreign import javascript unsafe "$1.preventDefault()"
--   preventDefault :: ReactEvent -> IO ()

-- | Prevent further event propagation.
-- foreign import javascript unsafe "$1.stopPropagation()"
--   stopPropagation :: ReactEvent -> IO ()

-- | Get the document body.
foreign import javascript unsafe "document.body"
  documentBody :: DOMNode

-- | Check if an object has a particular field
foreign import javascript unsafe "($2[$1] != null)"
  hasProp :: JSString -> JSVal -> Bool

-- | Extract a String field from a JS object.
-- TODO: This is unsafe (if the field doesn't exist)
foreign import javascript unsafe "($2[$1])"
  getProp :: JSString -> JSVal -> JSString

-- | Extract an object field from a JS object.
-- TODO: This is unsafe (if the field doesn't exist)
foreign import javascript unsafe "($2[$1])"
  getPropObj :: JSString -> JSVal -> JSVal

-- | Create an detached dom element.
foreign import javascript unsafe "document.createElement(\"div\")"
  documentCreateElement :: JSString -> IO DOMNode

-- | Append an element to another.
foreign import javascript unsafe "$1.appendChild($2)"
  appendChild :: DOMNode -> DOMNode -> IO ()

-- | Print strings to the console.
foreign import javascript unsafe "console.log($1)"
  consoleLog :: JSString -> IO ()

-- | Print objects to the console.
foreign import javascript unsafe "console.log($1)"
  consoleLogObj :: JSVal -> IO ()


-- AJ: These two functions should be in ghcjs-prim

-- | Convert JS Val to Bool>
foreign import javascript unsafe "$r = typeof($1) === 'boolean' ? $1: false;"
  fromJSBool :: JSVal -> Bool

-- | Convert Bool to JS Val.
foreign import javascript unsafe "$r = $1;"
  toJSBool :: Bool -> JSVal
