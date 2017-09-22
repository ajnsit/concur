module Concur.Internal.ReactFFI where

import           GHCJS.Foreign.Callback (Callback)
import           GHCJS.Types            (JSString, JSVal)
import           JavaScript.Array       (JSArray)
import           JavaScript.Object      (Object)

-- | Perform an action at the next animation frame.
foreign import javascript unsafe "window.requestAnimationFrame($1)"
  js_requestAnimationFrame :: Callback (IO ()) -> IO ()

-- Render a React App
foreign import javascript unsafe "h$concur.ReactDOM.render($2, $1)"
  js_renderReactDOM :: JSVal -> JSVal -> IO ()

-- | PURE: Construct a react dom node with children.
foreign import javascript unsafe "h$concur.React.createElement($1, $2, $3)"
  js_mkReactParent :: JSVal -> Object -> JSArray -> JSVal

-- | PURE: Construct a react dom node without children.
foreign import javascript unsafe "h$concur.React.createElement($1, $2)"
  js_mkReactLeaf :: JSVal -> Object -> JSVal

-- | PURE: Construct a text dom node.
foreign import javascript unsafe "$r = $1;"
  js_mkText :: JSString -> JSVal

-- | Prevent the default event action from taking place.
-- foreign import javascript unsafe "$1.preventDefault()"
--   preventDefault :: ReactEvent -> IO ()

-- | Prevent further event propagation.
-- foreign import javascript unsafe "$1.stopPropagation()"
--   stopPropagation :: ReactEvent -> IO ()

-- | Get the document body.
foreign import javascript unsafe "document.body"
  js_documentBody :: JSVal

-- | Check if an object has a particular field
foreign import javascript unsafe "($2[$1] != null)"
  js_hasProp :: JSString -> JSVal -> Bool

-- | Extract a String field from a JS object.
-- TODO: This is unsafe (if the field doesn't exist)
foreign import javascript unsafe "($2[$1])"
  js_getProp :: JSString -> JSVal -> JSString

-- | Extract an object field from a JS object.
-- TODO: This is unsafe (if the field doesn't exist)
foreign import javascript unsafe "($2[$1])"
  js_getPropObj :: JSString -> JSVal -> JSVal

-- | Create an detached dom element.
foreign import javascript unsafe "document.createElement(\"div\")"
  js_documentCreateElement :: JSString -> IO JSVal

-- | Append an element to another.
foreign import javascript unsafe "$1.appendChild($2)"
  js_appendChild :: JSVal -> JSVal -> IO ()

-- | Print strings to the console.
foreign import javascript unsafe "console.log($1)"
  js_consoleLog :: JSString -> IO ()

-- | Print objects to the console.
foreign import javascript unsafe "console.log($1)"
  js_consoleLogObj :: JSVal -> IO ()


-- AJ: These two functions should be in ghcjs-prim

-- | Convert JS Val to Bool>
foreign import javascript unsafe "$r = typeof($1) === 'boolean' ? $1: false;"
  js_fromJSBool :: JSVal -> Bool

-- | Convert Bool to JS Val.
foreign import javascript unsafe "$r = $1;"
  js_toJSBool :: Bool -> JSVal
