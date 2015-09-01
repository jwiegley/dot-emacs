{-# OPTIONS -cpp #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
module Set60204 where

#if __GLASGOW_HASKELL__ >= 604 
import qualified Data.Set as S
differenceS = S.difference
unionsS = S.unions
intersectionS = S.intersection 
fromListS = S.fromList
emptyS = S.empty
memberS = S.member
mapS = S.map
elemsS = S.elems
unionS = S.union
#else
import qualified Sets as S
difference = S.minusSet
unionsS = S.unionManySets
intersectionS=S.intersect
fromListS = S.mkSet
emptyS = S.emptySet
memberS = S.elementOf
mapS = S.mapSet
elemsS = S.setToList
unionS = S.union
#endif
