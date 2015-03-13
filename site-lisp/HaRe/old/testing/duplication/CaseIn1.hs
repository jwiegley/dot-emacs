module CaseIn1 where

--A local definition declared in a case alternative can be duplicated.

--duplicate the local definition 'x' with new defintion name 'y'

main :: (Int, Int)
main = (silly [2,3,5,1], silly [4])

silly :: [Int] -> Int
silly list = case list of
              (1:xs) -> 1
              (2:xs)
                | x < 10    -> 4
                   where
                     x::[Int]->Int
                     x = last xs                 
              otherwise -> 12 
