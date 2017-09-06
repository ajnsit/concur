{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE GHCForeignImportPrim #-}
{-# LANGUAGE MagicHash #-}

module Concur.React.Internal where

import Unsafe.Coerce (unsafeCoerce)

import GHCJS.Foreign.QQ (js')
import GHCJS.Types (JSString, JSVal)
import GHC.Base         (Any)

import Concur.React.Attributes (Attribute(Attribute))

-- `a` must be a newtype of JSVal!
mkEventAttr :: JSString -> (a -> IO ()) -> Attribute
mkEventAttr attr h =
  let e  = unsafeExportValue h
      h' = [js'| h$concur.makeHandler(`e, false) |]
  in  h' `seq` Attribute attr h'
{-# INLINE mkEventAttr #-}

-- -----------------------------------------------------------------------------
{-|
   Export an arbitrary Haskell value to JS.

   be careful with these JSVal values, losing track of them will result in
   incorrect memory management. As long as we keep the values directly in
   a Property or VNode, the ghcjs-vdom extensible retention system will know
   where to find them.
 -}
unsafeExportValue :: a -> JSVal
unsafeExportValue x = js_export (unsafeCoerce x)
{-# INLINE unsafeExportValue #-}

foreign import javascript unsafe "$r = $1;" js_export :: Any -> JSVal
