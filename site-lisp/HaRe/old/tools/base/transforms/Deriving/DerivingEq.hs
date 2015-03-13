module DerivingEq where
import DerivingUtils

deriveEq stdnames src t@(_,TypeInfo{constructors=cs}) =
  do let pv = stdvalue stdnames mod_Prelude
     HsVar eq <- pv "=="
     true <- pv "True"
     false <- pv "False"
     andand <- pv "&&"
     let def = if length cs>1
	       then [alt2 src eq wild wild (ident false)]
	       else []
	 eqalt ConInfo{conName=c0,conArity=n} =
	    alt2 (srcLoc c0) eq (p xs) (p ys) rhs
	   where
	     c = convCon t c0
	     p vs = hsPApp c vs
	     rhs = conj andand true comps
	     comps = zipWith eqtst xs ys
	     eqtst = opapp (HsVar eq)
	     xs=take n (vars "x")
	     ys=take n (vars "y")

     return [fun src (map eqalt cs++def)]
