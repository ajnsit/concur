{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeFamilies          #-}
module Concur.Doom.Types where

import           Data.IntMap (IntMap)
import qualified Data.Map    as M
import           Data.Maybe  (mapMaybe)

import           Data.Align  (Align) -- , alignWith)
import qualified Data.Align  as A
import           Data.These  (These (..))

import           Diferencia

-- Finally tagless representation of a DOM Tree
data DomTree c
  = DomList !String ![DomAttr] ![c]
  -- Keyed children nodes for efficiency
  | DomKeys !String ![DomAttr] !(IntMap c)
  | DomLeaf !String ![DomAttr]
  | DomText !String
  | DomNil
  deriving (Eq, Functor)

fetchAttr :: DomTree c -> [DomAttr]
fetchAttr (DomList _ a _) = a
fetchAttr (DomKeys _ a _) = a
fetchAttr (DomLeaf _ a)   = a
fetchAttr _               = []

instance Eq (Expr DomTree) where
  (==) (Expr t1) (Expr t2) = t1 == t2

type DomAttr = (String, String)

-- Dom Node Modifications
-- Either del or set
newtype DomOp = DomOp { unDomOp :: [Either String DomAttr] }

-- Dom Expressions
type DomExpr  = Expr DomTree
type DomEdit  = Editor DomTree
type DomState = EditState DomTree

diffNode
  :: (NodeEditOp f ~ DomOp, Eq a)
  => a -> [DomAttr]
  -> a -> [DomAttr]
  -> Expr (Edit (Expr f) (Expr f) f)
  -> Expr (Edit (Expr f) (Expr f) f)
  -> Expr (Edit (Expr f) (Expr f) f)
diffNode n1 a1 n2 a2 e r =
  if n1 == n2
  then
    if a1 == a2
    then e
    else esNodeEdit (diffAttr a1 a2) e
  else r

instance NodeEditable DomTree where
  type NodeEditOp DomTree = DomOp
  editNode       :: DomTree a -> DomOp -> DomTree a
  editNode (DomList n a c) o = DomList n (patchAttr o a) c
  editNode (DomKeys n a c) o = DomKeys n (patchAttr o a) c
  editNode (DomLeaf n a) o   = DomLeaf n (patchAttr o a)
  editNode d@(DomText _) _   = d
  editNode DomNil _ = DomNil
  revertNodeEdit :: DomTree a -> DomOp -> DomOp
  revertNodeEdit t as = DomOp (mapMaybe revert (unDomOp as))
    where
      amap = M.fromList (fetchAttr t)
      revert (Left s)      = Right . (s,) <$> M.lookup s amap
      revert (Right (s,_)) = Just (Left s)

-- Diffing trees
instance Diffable DomTree where
  diffExpr l1@(Expr (DomLeaf n1 a1)) l2@(Expr (DomLeaf n2 a2)) =
    diffNode n1 a1 n2 a2 (keep l1) (esRep l1 l2)
  diffExpr l1@(Expr (DomList n1 a1 m1)) l2@(Expr (DomList n2 a2 m2)) =
    diffNode n1 a1 n2 a2 (esEdit (DomList n1 a1 (diffList m1 m2))) (esRep l1 l2)
  diffExpr l1@(Expr (DomKeys n1 a1 m1)) l2@(Expr (DomKeys n2 a2 m2)) =
    diffNode n1 a1 n2 a2 (esEdit (DomKeys n1 a1 (diffKeys m1 m2))) (esRep l1 l2)
  diffExpr t1 t2 = esRep t1 t2

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

diffAttr :: [DomAttr] -> [DomAttr] -> DomOp
diffAttr l1 l2 = DomOp $ as ++ bs
  where
    m1 = M.fromList l1
    m2 = M.fromList l2
    cs = M.intersection m1 m2
    as = Left <$> M.keys (M.difference m1 cs)
    bs = Right <$> M.toList (M.difference m2 cs)

patchAttr :: DomOp -> [DomAttr] -> [DomAttr]
patchAttr o as = M.toList (foldr f amap (unDomOp o))
  where
    amap = M.fromList as
    f (Left s)      = M.delete s
    f (Right (a,b)) = M.insert a b
