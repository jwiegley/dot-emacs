module FunIn1 where
foo x
    =   let x = 12
	     
	    prod = ((x * 5) * z) * w
	in prod
  where
      z = 3
      w = 5
 
main = foo 10
 