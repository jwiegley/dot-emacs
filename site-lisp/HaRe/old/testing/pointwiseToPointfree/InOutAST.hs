module InOut where
import PointlessP.Functors
import PointlessP.Combinators
import PointlessP.Isomorphisms
import PointlessP.RecursionPatterns
tail'
    =   app .
	    (((curry
		   (app .
			((curry
			      ((((inN (_L :: [a])) . (Left . bang)) \/ snd) .
				   distr)) /\
			     ((ouT (_L :: [a])) . snd)))) .
		  bang) /\
		 id)
 