module Concur.Doom where

import           Data.IntMap       (IntMap)

import           Diferencia

import           Concur.Doom.Types

-- Expressions

text :: String -> Expr DomTree
text s = Expr (DomText s)

nodeList :: String -> [DomAttr] -> [Expr DomTree] -> Expr DomTree
nodeList n a c = Expr (DomList n a c)

nodeKeys :: String -> [DomAttr] -> IntMap (Expr DomTree) -> Expr DomTree
nodeKeys n a c = Expr (DomKeys n a c)

leaf :: String -> [DomAttr] -> Expr DomTree
leaf n a = Expr (DomLeaf n a)

h1 :: [DomAttr] -> String -> Expr DomTree
h1 a s = nodeList "h1" a [text s]

-- Edit ops

-- This widget should be equivalent to
