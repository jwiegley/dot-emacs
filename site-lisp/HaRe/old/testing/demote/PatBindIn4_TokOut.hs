module PatBindIn4 where

--A definition can be demoted to the local 'where' binding of a friend declaration,
--if it is only used by this friend declaration.

--Demoting a definition narrows down the scope of the definition.
--In this example, demote the top level 'tup' will fail.

main :: Int
main = foo 3

foo :: Int -> Int
foo x = h + t + (snd tup)

tup :: (Int, Int)
h :: Int
t :: Int
tup@(h,t) = head $ zip [1..10] [3..15]

fun=h 

