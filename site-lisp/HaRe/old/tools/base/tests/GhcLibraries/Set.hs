-- A dummy Set module...
module Set where

newtype Set a = Set [a]

emptySet :: Set a
mkSet :: Ord a => [a] -> Set a
setToList :: Set a -> [a]
unionManySets :: Ord a => [Set a] -> Set a
intersect, union, minusSet :: Ord a => Set a -> Set a -> Set a
mapSet :: Ord b => (a->b) -> Set a -> Set b
elementOf :: Ord a => a -> Set a -> Bool

emptySet = undefined
mkSet = undefined
setToList = undefined
unionManySets = undefined
minusSet = undefined
mapSet = undefined
intersect = undefined
union = undefined
elementOf = undefined
