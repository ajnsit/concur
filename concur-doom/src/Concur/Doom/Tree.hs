{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeFamilies          #-}
module Concur.Doom.Tree where

import           Data.IntMap (IntMap)
import qualified Data.Map    as M
import           Data.Maybe  (mapMaybe)

import           Data.Align  (Align) -- , alignWith)
import qualified Data.Align  as A
import           Data.These  (These (..))

import           Diferencia

import Concur.Doom.Attrs

-------------------------------------------------------------------------------
-- Finally tagless representation of a DOM Tree
data DomTree c
  = DomList !String ![DomAttr] ![c]
  -- Keyed children nodes for efficiency
  | DomKeys !String ![DomAttr] !(IntMap c)
  | DomLeaf !String ![DomAttr]
  | DomText !String
  | DomNil
  deriving (Show, Eq, Functor)

-- Instances that cannot be derived in a generic fashion
instance Eq DomExpr where
  (==) (Expr t1) (Expr t2) = t1 == t2

instance Show DomExpr where
  show (Expr t1) = show t1

instance Show DomEdit where
  show (Expr t1) = show t1

instance Show DomState where
  show (Expr t1) = show t1

-- Type aliases for Dom Expressions
type DomExpr  = Expr DomTree
type DomEdit  = Editor DomTree
type DomState = EditState DomTree

-------------------------------------------------------------------------------
-- Constructors
elText :: String -> DomExpr
elText s = Expr (DomText s)

elList :: String -> [DomAttr] -> [DomExpr] -> DomExpr
elList n a c = Expr (DomList n a c)

elKeys :: String -> [DomAttr] -> IntMap (DomExpr) -> DomExpr
elKeys n a c = Expr (DomKeys n a c)

elLeaf :: String -> [DomAttr] -> DomExpr
elLeaf n a = Expr (DomLeaf n a)

-------------------------------------------------------------------------------
-- Sample trees
sample1 :: DomExpr
sample1 = elList "div" []
  [ elList "h1" [] [elText "Hello Sample!"]
  , elList "p" []
    [ elList "h2" [] [elText "This is a paragraph heading"]
    , elList "p" [] [elText "Enter some info in the textbox below -"]
    , elList "p" []
      [ elLeaf "input" [("type", "text")]
      ]
    ]
  ]

sample2 :: DomExpr
sample2 = elList "div" []
  [ elList "h2" [] [elText "Hello NEW Sample!"]
  , elList "p" []
    [ elList "h2" [] [elText "This is a paragraph heading"]
    , elList "p" [] [elText "Enter some info in the textbox below -"]
    , elList "p" []
      [ elLeaf "input" [("type", "text")]
      ]
    ]
  ]

-- Sample edit ops
-- Delete the first child of the top level div
sampleEdit1 :: DomEdit
sampleEdit1 = eEdit $ DomList "h1" [] [ eDel ]

-------------------------------------------------------------------------------
-- Ops on DomTrees
fetchTag :: DomTree c -> Maybe String
fetchTag (DomList n _ _) = Just n
fetchTag (DomKeys n _ _) = Just n
fetchTag (DomLeaf n _)   = Just n
fetchTag _               = Nothing

fetchAttrs :: DomTree c -> [DomAttr]
fetchAttrs (DomList _ a _) = a
fetchAttrs (DomKeys _ a _) = a
fetchAttrs (DomLeaf _ a)   = a
fetchAttrs _               = []

-------------------------------------------------------------------------------
-- Comparing DomExprs
sameTopLevelData :: DomExpr -> DomExpr -> Bool
sameTopLevelData l1 l2 = sameTopLevelTag l1 l2 && sameTopLevelAttrs l1 l2

sameTopLevelTag :: DomExpr -> DomExpr -> Bool
sameTopLevelTag l1 l2 = fetchTag (unExpr l1) == fetchTag (unExpr l2)

sameTopLevelAttrs :: DomExpr -> DomExpr -> Bool
sameTopLevelAttrs l1 l2 = fetchAttrs (unExpr l1) == fetchAttrs (unExpr l2)


-------------------------------------------------------------------------------
-- Expression instances

instance NodeEditable DomTree where
  -- Dom Node Modifications
  -- For now, the only thing we allow is modifying the attributes
  type NodeEditOp DomTree = DomAttrOp
  editNode :: DomTree a -> NodeEditOp DomTree -> DomTree a
  editNode (DomList n a c) o = DomList n (patchAttr o a) c
  editNode (DomKeys n a c) o = DomKeys n (patchAttr o a) c
  editNode (DomLeaf n a) o   = DomLeaf n (patchAttr o a)
  editNode d@(DomText _) _   = d
  editNode DomNil _ = DomNil
  revertNodeEdit :: DomTree a -> NodeEditOp DomTree -> NodeEditOp DomTree
  revertNodeEdit t as = DomAttrOp (mapMaybe revert (unDomAttrOp as))
    where
      amap = M.fromList (fetchAttrs t)
      revert (Left s)      = Right . (s,) <$> M.lookup s amap
      revert (Right (s,_)) = Just (Left s)

-- Diffing trees
instance Diffable DomTree where
  diffExpr = go
    where
      -- Structural diff
      go l1@(Expr (DomLeaf {})) l2@(Expr (DomLeaf {})) =
        diffNode l1 l2 (keep l1)
      go l1@(Expr (DomList n1 a1 m1)) l2@(Expr (DomList _ _ m2)) =
        diffNode l1 l2 (esEdit (DomList n1 a1 (diffList m1 m2)))
      go l1@(Expr (DomKeys n1 a1 m1)) l2@(Expr (DomKeys _ _ m2)) =
        diffNode l1 l2 (esEdit (DomKeys n1 a1 (diffKeys m1 m2)))
      -- If the structures don't match, just replace
      go l1 l2 = esRep l1 l2
      -- Escalating levels of edits - 1. Node edit 2. Node edit + edit attrs 3. Replace
      diffNode l1 l2 e
        | sameTopLevelData l1 l2 = e
        | sameTopLevelTag l1 l2 = esNodeEdit (diffAttr (fetchAttrs $ unExpr l1) (fetchAttrs $ unExpr l2)) e
        | otherwise = esRep l1 l2

instance Align DomTree where
  nil = DomNil
  -- Structural alignment
  align (DomList n1 a1 c1) (DomList _ _ c2) = DomList n1 a1 (A.align c1 c2)
  align (DomKeys n1 a1 c1) (DomKeys _ _ c2) = DomKeys n1 a1 (A.align c1 c2)
  -- Nil handling
  align DomNil (DomList n2 a2 c2)             = DomList n2 a2 (fmap That c2)
  align DomNil (DomKeys n2 a2 c2)             = DomKeys n2 a2 (fmap That c2)
  align DomNil (DomLeaf n2 a2)                = DomLeaf n2 a2
  align DomNil (DomText t2)                   = DomText t2
  -- For mismatches of structure, just ignore the second
  -- TODO: Handle mismatches more gracefully
  align (DomList n1 a1 c1) _ = DomList n1 a1 (fmap This c1)
  align (DomKeys n1 a1 c1) _ = DomKeys n1 a1 (fmap This c1)
  align (DomLeaf n1 a1) _ = DomLeaf n1 a1
  align (DomText s) _ = DomText s
  align DomNil _ = DomNil

instance Expression DomTree
