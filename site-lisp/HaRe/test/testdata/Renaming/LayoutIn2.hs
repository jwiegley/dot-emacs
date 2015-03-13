module LayoutIn2 where

--Layout rule applies after 'where','let','do' and 'of'

--In this Example: rename 'list' to 'ls'.

silly :: [Int] -> Int
silly list = case list of  (1:xs) -> 1
--There is a comment
                           (2:xs)
                             | x < 10    -> 4  where  x = last xs 
                           otherwise -> 12 

