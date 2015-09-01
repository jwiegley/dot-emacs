module PatBindIn2 where

--A definition can be lifted from a where or let into the surrounding binding group.
--Lifting a definition widens the scope of the definition.

--In this example, lift 'tup' defined in  'foo' will fail.

main :: Int
main = foo 3

foo :: Int -> Int
foo x = h + t + (snd tup)
      where
      h :: Int
      t :: Int
      tup :: (Int,Int)
      tup@(h,t) = head $ zip [1..x] [3..15]
