module Concur.Doom.Attrs where

import qualified Data.Map    as M

-- Temporary Attr representation for simplicity
type DomAttr = (String, String)

-- Attribute Modifications
-- Either del or set
newtype DomAttrOp = DomAttrOp { unDomAttrOp :: [Either String DomAttr] }
  deriving (Show, Eq)

diffAttr :: [DomAttr] -> [DomAttr] -> DomAttrOp
diffAttr l1 l2 = DomAttrOp $ as ++ bs
  where
    m1 = M.fromList l1
    m2 = M.fromList l2
    cs = M.intersection m1 m2
    as = Left <$> M.keys (M.difference m1 cs)
    bs = Right <$> M.toList (M.difference m2 cs)

patchAttr :: DomAttrOp -> [DomAttr] -> [DomAttr]
patchAttr o as = M.toList (foldr f amap (unDomAttrOp o))
  where
    amap = M.fromList as
    f (Left s)      = M.delete s
    f (Right (a,b)) = M.insert a b
