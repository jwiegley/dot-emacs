module Abs where
import PointlessP.Combinators
import PointlessP.Functors
import PointlessP.Isomorphisms
import PointlessP.RecursionPatterns
fun =   app .
	    (((curry (curry (curry ((snd . fst) . fst)))) .
		  bang) /\
		 id)
 