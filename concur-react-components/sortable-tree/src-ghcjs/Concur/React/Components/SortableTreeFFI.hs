module Concur.React.Components.SortableTreeFFI where

import           GHCJS.Types (JSVal)

-- | PURE: Access to the SortableTree component
foreign import javascript unsafe "h$ffi.SortableTree"
  js_sortableTreeComponent :: JSVal
