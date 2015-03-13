module Case where
import PointlessP.Combinators
import PointlessP.Functors
import PointlessP.Isomorphisms
import PointlessP.RecursionPatterns
coswap
    =   app .
	    (((curry
		   (app .
			((curry (((Right . snd) \/ (Left . snd)) . distr)) /\
			     snd))) .
		  bang) /\
		 id)
 