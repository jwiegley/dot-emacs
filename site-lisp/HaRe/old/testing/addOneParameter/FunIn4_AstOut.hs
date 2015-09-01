module FunIn4 where
main :: Int
 
main
    =   sum [x + 4 | let foo y = [1 .. 4]
			  
			 foo_y = undefined,
		     x <- (foo foo_y)]
 