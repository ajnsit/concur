module Concur.SDL.Painter where

import SDL (Renderer, Event)

-- A "View" is basically a painting function that puts things on the screen
data Painter = Painter { paint :: Renderer -> [Event] -> IO () }

instance Monoid Painter where
  mempty = Painter $ \_ _ -> pure ()
  mappend a b = Painter (\r e -> paint a r e >> paint b r e)
