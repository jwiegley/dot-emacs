module FunIn2 where
main :: Int -> Int
 
main
    =   \ x ->
            case x of
                1 -> 1 + (main 0)
                0 -> ((1 + 2) + 3)
 
addthree :: Int -> Int -> Int -> Int
 
addthree a b c = (a + b) + c
 