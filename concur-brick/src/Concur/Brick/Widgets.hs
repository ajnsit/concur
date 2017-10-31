{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts  #-}
module Concur.Brick.Widgets where

import qualified Graphics.Vty.Image as I
import qualified Graphics.Vty.Attributes as A

import Data.Text.Lazy (Text)

import Control.MonadShiftMap
import Concur.Core
import Concur.Brick.Run

-- Horizontal composition
horz :: MonadShiftMap (Widget View) m => m a -> m a
horz = shiftMap (wrapView I.horizCat)

-- Vertical composition
vert :: MonadShiftMap (Widget View) m => m a -> m a
vert = shiftMap (wrapView I.vertCat)

-- Text
text :: A.Color -> Text -> Widget View x
text color s = display [I.text (A.defAttr `A.withForeColor` color) s]
