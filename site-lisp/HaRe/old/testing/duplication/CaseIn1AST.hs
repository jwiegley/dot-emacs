module CaseIn1 where
main :: (Int, Int)
 
main = (silly [2, 3, 5, 1], silly [4])
 
silly :: [Int] -> Int
 
silly list
    =   case list of
            (1 : xs) -> 1
            (2 : xs)
                | x < 10 -> 4
              where
                  x :: [Int] -> Int
                  x = last xs
                  y :: [Int] -> Int
                  y = last xs
            otherwise -> 12
 