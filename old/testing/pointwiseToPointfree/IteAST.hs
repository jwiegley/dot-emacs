module Ite where
import PointlessP.Combinators
import PointlessP.Functors
import PointlessP.Isomorphisms
import PointlessP.RecursionPatterns
notZero
    =   app .
	    (((curry
		   (app .
			((curry
			      ((((inN (_L :: Bool)) . (Right . bang)) \/
				    ((inN (_L :: Bool)) . (Left . bang))) .
				   distr)) /\
			     ((ouT (_L :: Bool)) .
				  (app .
				       ((curry
					     ((((inN (_L :: Bool)) .
						    (Left . bang)) \/
						   ((inN (_L :: Bool)) .
							(Right . bang))) .
						  distr)) /\
					    ((ouT (_L :: Int)) . snd))))))) .
		  bang) /\
		 id)
 