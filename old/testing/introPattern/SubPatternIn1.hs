module SubPatternIn1 where

-- allow the user to select 'c' on the LHS of 
-- f. Should introduce 2 new equations for f:
-- f z 

data T = C1 [Int] Int [Float]| C2 Int

g :: Int -> T -> Int
g z (C1 x b c) = x
g z (C2 x) = x

f :: [Int] -> Int
f x@[] = hd x + hd (tl x)
f x@(y:ys) = hd x + hd (tl x)


hd x = head x

tl x = tail x
 