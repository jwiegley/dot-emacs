module SubPatternIn3 where

-- takes into account general type variables
-- within type implementation.
-- here T has its arguments instantiated within g
-- selecting 'b' should instantiate list patterns
-- selecting 'c' should give an error.
-- 

data T a b = C1 a b | C2 b

g :: Int -> T Int [Int] -> Int
g z (C1 b c) = b
g z (C2 x@[]) = hd x
g z (C2 x@(b_1 : b_2)) = hd x
g z (C2 x) = hd x

f :: [Int] -> Int
f x@[] = hd x + hd (tl x)
f x@(y:ys) = hd x + hd (tl x)


hd x = head x

tl x = tail x
 