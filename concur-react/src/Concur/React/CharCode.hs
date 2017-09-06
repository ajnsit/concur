-- | The DOM has two ways of describing keyboard events: by Keycode, or by
-- Charcode. The Keycode represents the physical key which was involved,
-- whereas the Charcode represents the resulting character. Therefore, a
-- typical keyboard interaction might yeild the following events:
--
-- > KeyDown KeyCode.shift
-- > KeyDown KeyCode.letterA
-- > KeyPress (CharCode.fromChar 'A')
-- > KeyUp KeyCode.letterA
-- > KeyUp KeyCode.shift
module Concur.React.CharCode
    ( Charcode
    , unCharcode
    , fromChar
    ) where

-- | A representation of an ASCII character.
newtype Charcode = Charcode { unCharcode :: Int }
    deriving (Eq, Ord, Show)

-- TODO (AS): Make explicit constructors, or perhaps a quasi-quotation.
fromChar :: Char -> Charcode
fromChar c = case fromEnum c of
    x | x < 128 -> Charcode x -- It's ASCII
_ -> error "mkCharcode: Not ASCII"
