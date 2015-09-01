module GuardsIn2 where

merge :: (a -> a -> Ordering) -> [a] -> [a] -> [a]
merge cmp xs [] = xs
merge cmp [] ys = ys
merge cmp (x:xs) (y:ys)
 = case x `cmp` y of
        GT -> y : merge cmp (x:xs)   ys
        _  -> x : merge cmp    xs (y:ys)



{- mergeIt xs ys = merge compare xs ys -}



mergeIt :: (a -> a -> Ordering) -> [a] -> [a] -> [a]

mergeIt xs ys = merge compare xs ys
mergeIt xs [] = xs
mergeIt [] ys = ys
mergeIt (x:xs) (y:ys)
 | x `compare` y == GT = y : merge compare (x:xs) ys
 | otherwise           = x : merge compare xs (y:ys)



{- select first occurrence of merge cmp (x:xs) ys to replace it with
     mergeIt (x:xs) ys

-}


