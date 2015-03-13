module NegativeIn1 where

--The application of a function is replaced by the right-hand side of the definition,
--with actual parameters replacing formals.

--In this example, unfold the 'snd' will fail.

main :: Int
main = foo 3

foo :: Int -> Int
foo x = h + t + (snd tup)  where t::Int
                                 h::Int
                                 tup :: (Int,Int)
                                 tup@(h,t) = head $ zip [1..x] [3..15]
   