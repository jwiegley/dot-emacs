module FunIn3 where
f z x y = (x + y) + z
 
g   =   (f   (let z1 = 10
		   
		  z2 = 20
	      in z1 + z2)
	     10
	     20) +
	    (f   (let z1 = 10
		       
		      z2 = 20
		  in z1 + z2)
		 20
		 40)
 