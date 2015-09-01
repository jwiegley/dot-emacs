module WhereIn6 where

--duplicate a complex pattern binding or a definition which is not defined in
--this module  will fail.
--In This Example: duplicate 'tup','h' or 't' will fail.(Is this reasonable?)

main :: Int
main = foo 3

foo :: Int -> Int
foo x = h + t + (snd tup)
      where
      h :: Int
      t :: Int
      tup :: (Int,Int)
      tup@(h,t) = head $ zip [1..x] [3..15]


