module DerivingOrd where
import Data.Maybe(mapMaybe)
import DerivingUtils

deriveOrd stdnames src t@(_,TypeInfo{constructors=cs}) =
  do let pv = stdvalue stdnames mod_Prelude
         pt = stdtype stdnames mod_Prelude
     HsVar compare <- pv "compare"
     lexOrder <- pv "lexOrder" -- nonstandard entity!
     int <- hsTyId # pt "Int"
     let branches = mapMaybe eqbranch cs `asTypeOf` def
	 n = length cs
	 def = if n<2 && length branches==n
	       then []
	       else [alt x y cmpcno]
	   where
	     x = var (localVal "x")
	     y = var (localVal "y")
	     cmpcno = hsLet cnodef (compareE (cnoE x) (cnoE y))
	     cnodef = oneDef (fun src (zipWith cnoalt [0..] cs))
	     cno = localVal "cno"
	     cnoE a = var cno `app` a
	     cnoalt i ConInfo{conName=c0,conArity=n} = 
		  alt1 src cno (hsPApp c xs) (l i)
		where xs = replicate n wild
		      c = convCon t c0
	     l 0 = intlit 0 -:: int -- add type restriction to the first branch
	     l i = intlit i
	     intlit = hsLit src . HsInt
	 eqbranch ConInfo{conName=c0,conArity=n} =
	     if n==0
	     then Nothing
	     else Just (alt (p xs) (p ys) rhs)
	   where
	     c = convCon t c0
	     p = hsPApp c
	     rhs = conj comps
	     conj = foldr1 (opapp lexOrder)
	     comps = zipWith compareE xs ys
	     xs = take n (vars "x")
	     ys = take n (vars "y")

	 compareE = opapp (HsVar compare)

	 alt = alt2 src compare

     return [fun src (branches++def)]
