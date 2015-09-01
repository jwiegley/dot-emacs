module LayoutIn2 where
silly :: [Int] -> Int
 
silly ls
    =   case ls of
	    ((1 : xs)) -> 1
	    ((2 : xs)) | x < 10 -> 4 where x = last xs
	    otherwise -> 12
 