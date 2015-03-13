module PartialIn1 where
main :: Int -> Int
 
main
    =   \ x ->
	    case x of
		1 -> 1 + (main 0)
		0 -> app (\ a b c -> (a + b) + c) 1 2 3
 
app :: (a -> b) -> a -> b
 
app = \ f x -> f x
 
addthree :: Int -> Int -> Int -> Int
 
addthree a b c = (a + b) + c
 