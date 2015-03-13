module RecNat where
import PointlessP.Combinators
import PointlessP.Functors
import PointlessP.Isomorphisms
import PointlessP.RecursionPatterns
recNat :: Int -> (Int -> a -> a) -> a -> a
 
recNat 0 f z = z
recNat n f z = f (n - 1) (recNat (n - 1) f z)
 
double
    =   app .
	    (((curry
		   ((para (_L :: Int)
			 (app .
			      (((curry
				     (app .
					  ((curry
						((((inN (_L :: Int)) .
						       (Left . bang)) \/
						      (app .
							   ((app .
								 ((curry
								       (curry
									    ((inN (_L :: Int)) .
										 (Right .
										      ((inN (_L :: Int)) .
											   (Right .
												snd)))))) /\
								      (snd .
									   snd))) /\
								(fst . snd)))) .
						     distr)) /\
					       snd))) .
				    bang) /\
				   id))) .
			snd)) .
		  bang) /\
		 id)
 