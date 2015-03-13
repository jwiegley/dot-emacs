module DerivingBounded where
import DerivingUtils

deriveBounded stdnames src t@(_,TypeInfo{constructors=cs}) =
  do let pv = stdvalue stdnames mod_Prelude
     HsVar minBound <- pv "minBound"
     HsVar maxBound <- pv "maxBound"
     let enumBounds cs@(c:_) = [b minBound c,b maxBound (last cs)]
	 b m ci = fun0 src m (con c)
	   where
	     c=convCon t (conName ci)

	 tupleBounds [ConInfo{conName=c0,conArity=n}] =
	     [tb minBound,tb maxBound]
	   where
	     tb m = fun0 src m (apps (con c:replicate n (var m)))
	     c=convCon t c0
     if isEnum cs
       then return (enumBounds cs)
       else if length cs == 1
            then return (tupleBounds cs)
            else fail "Deriving Bounded: the type is neither an enumeration nor a single constructor type."
