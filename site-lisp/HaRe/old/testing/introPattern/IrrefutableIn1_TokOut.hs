module IrrefutableIn1 where

-- test for irrefutable patterns

f :: [Int] -> Int
f (~x@[]) = hd x
f (~x@(b_1 : b_2)) = hd x
f (~x) = hd x

hd x = head x
tl x = tail x