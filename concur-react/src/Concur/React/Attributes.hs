{-# LANGUAGE QuasiQuotes              #-}
{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE GADTs        #-}
{-# LANGUAGE RankNTypes        #-}
module Concur.React.Attributes where

import qualified JavaScript.Object.Internal as OI
import qualified GHCJS.Prim.Internal.Build as IB
import           GHCJS.Types            (JSString, JSVal)
import GHCJS.Foreign.QQ
import Unsafe.Coerce (unsafeCoerce)

newtype Attributes' = Attributes' JSVal

data Attribute = Attribute JSString JSVal

class Attributes a where
  mkAttributes :: a -> Attributes'

instance Attributes Attributes' where
  mkAttributes x = x
  {-# INLINE mkAttributes #-}

instance Attributes () where
  mkAttributes _ = Attributes' [jsu'| {} |]
  {-# INLINE mkAttributes #-}

instance Attributes Attribute where
  mkAttributes (Attribute k v) =
    Attributes' (IB.buildObjectI1 (unsafeCoerce k) v)
  {-# INLINE mkAttributes #-}

instance Attributes [Attribute] where
  mkAttributes xs = Attributes' (IB.buildObjectI $
    map (\(Attribute k v) -> (unsafeCoerce k,v)) xs)
  {-# INLINE mkAttributes #-}
