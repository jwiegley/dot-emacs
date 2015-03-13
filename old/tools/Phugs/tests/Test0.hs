module Test0 where

id x = x
const x y = y

--fst (x,y) = x
--snd (x,y) = y

fac 0 = 1
fac n = n*fac(n-1)

one = 1

assert {fac 0} === one
