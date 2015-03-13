module CaseIn1 where
foo :: Int -> Int
 
foo x
    =   case x of
	    1 -> foo 0
	    0   ->  ((\ a b c -> addThree a b c) 1 2 3) +
			((\ y -> y + 1) 2)
	      where addThree a b c = (a + b) + c
 
main = foo 10
 