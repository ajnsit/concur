module Concur.Internal.ReactFFI where

import           GHCJS.Foreign.Callback (Callback)
import           GHCJS.Types            (JSString, JSVal)
import           JavaScript.Array       (JSArray)
import           JavaScript.Object      (Object)

-- | Perform an action at the next animation frame.
js_requestAnimationFrame :: Callback (IO ()) -> IO ()
js_requestAnimationFrame = error "js_requestAnimationFrame is unsupported on GHC"

-- Render a React App
js_renderReactDOM :: JSVal -> JSVal -> IO ()
js_renderReactDOM = error "js_renderReactDOM is unsupported on GHC"

-- | PURE: Construct a react dom node with children.
js_mkReactParent :: JSVal -> Object -> JSArray -> JSVal
js_mkReactParent = error "js_mkReactParent is unsupported on GHC"

-- | PURE: Construct a react dom node without children.
js_mkReactLeaf :: JSVal -> Object -> JSVal
js_mkReactLeaf = error "js_mkReactLeaf is unsupported on GHC"

-- | PURE: Construct a text dom node.
js_mkText :: JSString -> JSVal
js_mkText = error "js_mkText is unsupported on GHC"

-- | Prevent the default event action from taking place.
-- foreign import javascript unsafe "$1.preventDefault()"
--   preventDefault :: ReactEvent -> IO ()

-- | Prevent further event propagation.
-- foreign import javascript unsafe "$1.stopPropagation()"
--   stopPropagation :: ReactEvent -> IO ()

-- | Get the document body.
js_documentBody :: JSVal
js_documentBody = error "js_documentBody is unsupported on GHC"

-- | Check if an object has a particular field
js_hasProp :: JSString -> JSVal -> Bool
js_hasProp = error "js_hasProp is unsupported on GHC"

-- | Extract a String field from a JS object.
-- TODO: This is unsafe (if the field doesn't exist)
js_getProp :: JSString -> JSVal -> JSString
js_getProp = error "js_getProp is unsupported on GHC"

-- | Extract an object field from a JS object.
-- TODO: This is unsafe (if the field doesn't exist)
js_getPropObj :: JSString -> JSVal -> JSVal
js_getPropObj = error "js_getPropObj is unsupported on GHC"

-- | Create an detached dom element.
js_documentCreateElement :: JSString -> IO JSVal
js_documentCreateElement = error "js_documentCreateElement is unsupported on GHC"

-- | Append an element to another.
js_appendChild :: JSVal -> JSVal -> IO ()
js_appendChild = error "js_appendChild is unsupported on GHC"

-- | Print strings to the console.
js_consoleLog :: JSString -> IO ()
js_consoleLog = error "js_consoleLog is unsupported on GHC"

-- | Print objects to the console.
js_consoleLogObj :: JSVal -> IO ()
js_consoleLogObj = error "js_consoleLogObj is unsupported on GHC"


-- AJ: These two functions should be in ghcjs-prim

-- | Convert JS Val to Bool>
js_fromJSBool :: JSVal -> Bool
js_fromJSBool = error "js_fromJSBool is unsupported on GHC"

-- | Convert Bool to JS Val.
js_toJSBool :: Bool -> JSVal
js_toJSBool = error "js_toJSBool is unsupported on GHC"
