module InfixOp where
import PointlessP.Combinators
import PointlessP.Functors
import PointlessP.Isomorphisms
import PointlessP.RecursionPatterns
(.+.) _ n m = n + m
 
subt _ n m = n - m
 
calculate
    =   app .
	    (((curry
		   (curry
			(app .
			     ((app .
				   (((subt . fst) . fst) /\
					(app .
					     ((app .
						   (((subt . fst) . fst) /\
							(app .
							     ((app .
								   ((((.+.) .
									  fst) .
									 fst) /\
									(snd .
									     fst))) /\
								  (snd .
								       fst))))) /\
						  snd)))) /\
				  snd)))) .
		  bang) /\
		 id)
 