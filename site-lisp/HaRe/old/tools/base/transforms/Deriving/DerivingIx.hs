module DerivingIx where
import DerivingUtils
import DerivingEnum(fromToEnum)

{-+
When deriving #Ix# for an enumerations, the three operations (#range#, #index#,
 #inRange#) can easily be defined assuming you have auxiliary functions to
convert to and from Int. If there is a derived Enum instance,
toEnum and fromEnum could be used, but since we don't know if there is an
Enum instance, we define the same functions locally in each method definition.
This produces some code duplication. Grr!

Alternatively, the #inRange# method could be defined using (<=) from
the Ord class. We know that there is an Ord instance, since Ord is a
superclass of Ix, but we don't know if it is the derived Ord. A user
defined Ord instance can not be used. Grr again!
-}

deriveIx stdnames src t@(_,TypeInfo{constructors=cs}) =
  do let pv = stdvalue stdnames mod_Prelude
         pt = stdtype stdnames mod_Prelude
	 ixv = stdvalue stdnames mod_Ix
     int <- hsTyId # pt "Int"
     HsVar range <- ixv "range"
     HsVar index <- ixv "index"
     HsVar inRange <- ixv "inRange"
     rangeSize <- ixv "rangeSize"

     fromEnum@(HsVar fromE) <- pv "fromEnum"
     toEnum@(HsVar toE) <- pv "toEnum"
     true <- pv "True"
     andand <- pv "&&"
     map <- pv "map"
     plus  <- opapp # pv "+"
     times <- opapp # pv "*"
     let enumIx cs@(c:_) = [erange,eindex,einRange]
	   where
	     erange = pfun' range (l,u)
			    (mapE (ident toEnum)
				(apps [var range,pair (fromEnumE l) (fromEnumE u)]))
			    (toDefs fromto)

	     eindex = pfun2' index (l,u) i
			     (apps [var index,pair (fromEnumE l) (fromEnumE u),
					      fromEnumE i])
			     (oneDef from)

	     einRange = pfun2' inRange (l,u) i
			     (apps [var inRange,pair (fromEnumE l) (fromEnumE u),
						fromEnumE i])
			     (oneDef from)

	     fromto@[from,to] = fromToEnum src fromE toE t ( -:: int)

	     l = var (localVal "l")
	     u = var (localVal "u")
	     i = var (localVal "i")

	     fromEnumE = app (ident fromEnum)

	 -- pre: n>=1
	 tupleIx [ConInfo{conName=c0,conArity=n}] = [trange,tindex,tinRange]
	    where
	     trange = pfun range rpat $ hsListComp (foldr gen last (zip [1..] luis))
	       where
		 gen (n,(l,u,i)) =
		   HsGenerator (fakePos src n) i (var range `app` pair l u)
		 last = HsLast (apps (con c:is))

	     tindex = ilhs index $
		      case luis of
		       [lui] -> ix1 lui
		       _ -> foldl ix zero luis
	       where
		 ix1 (l,u,i) = apps [var index,pair l u,i]
		 ix acc (l,u,i) = ix1 (l,u,i) `plus`
				  ((ident rangeSize `app` pair l u) `times` acc)

	     tinRange = ilhs inRange $
			conj andand true [apps [var inRange,pair l u,i]|(l,u,i)<-luis]

	     ilhs f = pfun2 f rpat (hsPApp c is)
	     rpat = (hsPApp c ls,hsPApp c us)

	     c = convCon t c0
	     luis = zip3 ls us is
	     ls = take n (vars "l")
	     us = take n (vars "u")
	     is = take n (vars "i")

	 pfun f p rhs = pfun' f p rhs noDef
	 pfun' f (x,y) rhs ds = fun src [alt1' src f (pair x y) rhs ds]
	 pfun2 f p z rhs = pfun2' f p z rhs noDef
	 pfun2' f (x,y) z rhs ds = fun src [alt2' src f (pair x y) z rhs ds]

	 zero  = hsLit src (HsInt 0)

	 mapE f xs = apps [ident map,f,xs]

     if isEnum cs
       then return (enumIx cs)
       else if length cs == 1
            then return (tupleIx cs)
            else fail "Deriving Ix: the type is neither an enumeration nor a single constructor type."
