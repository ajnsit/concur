{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- | The DOM has two ways of describing keyboard events: by Keycode, or by
-- Charcode. The Keycode represents the physical key which was involved,
-- whereas the Charcode represents the resulting character. Therefore, a
-- typical keyboard interaction might yeild the following events:
--
-- > KeyDown Keycode.shift
-- > KeyDown Keycode.letterA
-- > KeyPress (Charcode.fromChar 'A')
-- > KeyUp Keycode.letterA
-- > KeyUp Keycode.shift
module Concur.React.KeyCode
    ( Keycode(..)

      -- * Constructors
    , backspace      , tab         , enter          , shift
    , ctrl           , alt         , pause          , capsLock
    , escape         , pageUp      , pageDown       , end
    , home           , leftArrow   , upArrow        , rightArrow
    , downArrow      , insert      , delete         , zero
    , one            , two         , three          , four
    , five           , six         , seven          , eight
    , nine           , letterA     , letterB        , letterC
    , letterD        , letterE     , letterF        , letterG
    , letterH        , letterI     , letterJ        , letterK
    , letterL        , letterM     , letterN        , letterO
    , letterP        , letterQ     , letterR        , letterS
    , letterT        , letterU     , letterV        , letterW
    , letterX        , letterY     , letterZ        , leftMeta
    , rightMeta      , select      , numpadZero     , numpadOne
    , numpadTwo      , numpadThree , numpadFour     , numpadFive
    , numpadSix      , numpadSeven , numpadEight    , numpadNine
    , numpadMultiply , numpadAdd   , numpadSubtract , numpadDecimalPoint
    , numpadDivide   , f1          , f2             , f3
    , f4             , f5          , f6             , f7
    , f8             , f9          , f10            , f11
    , f12            , numLock     , scrollLock     , semicolon
    , equals         , comma       , dash           , period
    , forwardslash   , graveAccent , openBracket    , backslash
    , closeBraket    , singleQuote
    ) where


-- | A representation of a physical key.
newtype Keycode = Keycode { unKeycode :: Int }
    deriving (Eq, Ord, Show)


-------------------------------------------------------------------------------
-- Safe constructors
-------------------------------------------------------------------------------

backspace          , tab         , enter          , shift
  , ctrl           , alt         , pause          , capsLock
  , escape         , pageUp      , pageDown       , end
  , home           , leftArrow   , upArrow        , rightArrow
  , downArrow      , insert      , delete         , zero
  , one            , two         , three          , four
  , five           , six         , seven          , eight
  , nine           , letterA     , letterB        , letterC
  , letterD        , letterE     , letterF        , letterG
  , letterH        , letterI     , letterJ        , letterK
  , letterL        , letterM     , letterN        , letterO
  , letterP        , letterQ     , letterR        , letterS
  , letterT        , letterU     , letterV        , letterW
  , letterX        , letterY     , letterZ        , leftMeta
  , rightMeta      , select      , numpadZero     , numpadOne
  , numpadTwo      , numpadThree , numpadFour     , numpadFive
  , numpadSix      , numpadSeven , numpadEight    , numpadNine
  , numpadMultiply , numpadAdd   , numpadSubtract , numpadDecimalPoint
  , numpadDivide   , f1          , f2             , f3
  , f4             , f5          , f6             , f7
  , f8             , f9          , f10            , f11
  , f12            , numLock     , scrollLock     , semicolon
  , equals         , comma       , dash           , period
  , forwardslash   , graveAccent , openBracket    , backslash
  , closeBraket    , singleQuote :: Keycode

backspace          = Keycode 8
tab                = Keycode 9
enter              = Keycode 13
shift              = Keycode 16
ctrl               = Keycode 17
alt                = Keycode 18
pause              = Keycode 19
capsLock           = Keycode 20
escape             = Keycode 27
pageUp             = Keycode 33
pageDown           = Keycode 34
end                = Keycode 35
home               = Keycode 36
leftArrow          = Keycode 37
upArrow            = Keycode 38
rightArrow         = Keycode 39
downArrow          = Keycode 40
insert             = Keycode 45
delete             = Keycode 46
zero               = Keycode 48
one                = Keycode 49
two                = Keycode 50
three              = Keycode 51
four               = Keycode 52
five               = Keycode 53
six                = Keycode 54
seven              = Keycode 55
eight              = Keycode 56
nine               = Keycode 57
letterA            = Keycode 65
letterB            = Keycode 66
letterC            = Keycode 67
letterD            = Keycode 68
letterE            = Keycode 69
letterF            = Keycode 70
letterG            = Keycode 71
letterH            = Keycode 72
letterI            = Keycode 73
letterJ            = Keycode 74
letterK            = Keycode 75
letterL            = Keycode 76
letterM            = Keycode 77
letterN            = Keycode 78
letterO            = Keycode 79
letterP            = Keycode 80
letterQ            = Keycode 81
letterR            = Keycode 82
letterS            = Keycode 83
letterT            = Keycode 84
letterU            = Keycode 85
letterV            = Keycode 86
letterW            = Keycode 87
letterX            = Keycode 88
letterY            = Keycode 89
letterZ            = Keycode 90
leftMeta           = Keycode 91
rightMeta          = Keycode 92
select             = Keycode 93
numpadZero         = Keycode 96
numpadOne          = Keycode 97
numpadTwo          = Keycode 98
numpadThree        = Keycode 99
numpadFour         = Keycode 100
numpadFive         = Keycode 101
numpadSix          = Keycode 102
numpadSeven        = Keycode 103
numpadEight        = Keycode 104
numpadNine         = Keycode 105
numpadMultiply     = Keycode 106
numpadAdd          = Keycode 107
numpadSubtract     = Keycode 109
numpadDecimalPoint = Keycode 110
numpadDivide       = Keycode 111
f1                 = Keycode 112
f2                 = Keycode 113
f3                 = Keycode 114
f4                 = Keycode 115
f5                 = Keycode 116
f6                 = Keycode 117
f7                 = Keycode 118
f8                 = Keycode 119
f9                 = Keycode 120
f10                = Keycode 121
f11                = Keycode 122
f12                = Keycode 123
numLock            = Keycode 144
scrollLock         = Keycode 145
semicolon          = Keycode 186
equals             = Keycode 187
comma              = Keycode 188
dash               = Keycode 189
period             = Keycode 190
forwardslash       = Keycode 191
graveAccent        = Keycode 192
openBracket        = Keycode 219
backslash          = Keycode 220
closeBraket        = Keycode 221
singleQuote        = Keycode 222
