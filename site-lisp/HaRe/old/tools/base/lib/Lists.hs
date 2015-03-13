module Lists (module Lists, module Data.List) where

import OpTypes
import Data.List
import Products

mergeOrd        :: OrdOp a -> [a] -> [a] -> [a]
merge           :: Ord a => [a] -> [a] -> [a]
unionMany       :: Eq a => [[a]] -> [a]
mapFst          :: (a -> x) -> [(a,b)] -> [(x,b)]
mapSnds         :: (b -> y) -> [(a, [b])] -> [(a, [y])]
mapFstSnds      :: (a -> x) -> (b -> y) -> [(a, [b])] -> [(x, [y])]
subset          :: Eq a => [a] -> [a] -> Bool

infixl 1 |$|
(|$|)           :: [a -> b] -> [a] -> [b]
(\\\)           :: Eq a => [a] -> [a] -> [a]


-- property srtedOrd leq xs     = (m `leq` n) ==> (xs !! m) `leq` (xs !! n)
-- property sorted              = sortedOrd (<=)

-- property noDuplEq eq xs      = (xs !! m) `eq` (xs !! n) ==> m === n
-- property noDupl              = noDupl (==) 

-- property mergeOrd  = sortedOrd leq xs /\ sortedOrd leq ys
--                          ==> sortedOrd leq (mergeOrd leq xs ys)
mergeOrd leq [] ys  = ys
mergeOrd leq xs []  = xs
mergeOrd leq a@(x:xs) b@(y:ys)
    | x `leq` y     = x : mergeOrd leq xs b
    | otherwise     = y : mergeOrd leq a ys 


-- property merge   = mergeOrd (<=)
merge = mergeOrd (<=)


singleton [_]   = True
singleton _     = False

xs `subset` ys  = all (`elem` ys) xs

unionMany       = nub . concat
mapFst f        = map (f >< id)
mapSnds g       = map (id >< map g)
mapFstSnds f g  = map (f >< map g) 

(|$|)           = zipWith ($)
xs \\\ ys       = filter (`notElem` ys) xs

--elemBy,notElemBy :: (a->a->Bool) -> a -> [a] -> Bool
elemBy eq x     = not . notElemBy eq x
notElemBy eq x  = null . filter (eq x)
