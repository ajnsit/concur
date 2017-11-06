{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Control.MultiAlternative where

import Control.Applicative (Alternative, empty, (<|>))

class MultiAlternative f where
  never :: f a
  orr :: [f a] -> f a

instance {-# OVERLAPPABLE #-} Alternative f => MultiAlternative f where
  never = empty
  orr = foldl (<|>) empty
