{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Control.MultiAlternative where

import Control.Applicative (Alternative, empty, (<|>))

class MultiAlternative f where
  orr :: [f a] -> f a

instance {-# OVERLAPPABLE #-} Alternative f => MultiAlternative f where
  orr = foldl (<|>) empty
