module DerivingShow where
import DerivingUtils

deriveShow stdnames src t@(_,TypeInfo{constructors=cs}) =
  do let pv = stdvalue stdnames mod_Prelude
     showParenArg <- pv "showParenArg"
     showArgument <- pv "showArgument"
     showString <- pv "showString"
     HsVar showsPrec <- pv "showsPrec"
     comp2 <- opapp # pv "."

     let showAlt ConInfo{conName=c0,conArity=n} =
	   case n of
	     0 -> alt (con c) (showConName cn)
	     _ -> alt (hsPApp c xs)
		      (paren (showConName cn `comp2` comp (map showArg xs)))
	   where
	     c = convCon t c0
	     cn = getBaseName c0
	     xs = take n (vars "x")

	 paren arg = ident showParenArg `app` d `app` arg
	 showArg v = ident showArgument `app` v
	 showConName c = ident showString `app` str src c

	 comp = foldr1 comp2

	 alt = alt2 src showsPrec d
	 d = var (localVal "d")

     return [fun src (map showAlt cs)]
