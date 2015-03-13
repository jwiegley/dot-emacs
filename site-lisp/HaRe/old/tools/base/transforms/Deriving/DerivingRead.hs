module DerivingRead where
import DerivingUtils

deriveRead stdnames src t@(_,TypeInfo{constructors=cs}) =
  do let pv = stdvalue stdnames mod_Prelude
     readParenArg <- pv "readParenArg"
     readArgument <- pv "readArgument"
     readToken <- pv "readToken"
     HsVar readsPrec <- pv "readsPrec"
     readAp <- pv "readAp"
     readChoice <- pv "readChoice"

     let d = var (localVal "d")

	 alt = alt1 src readsPrec d

	 rdCon ConInfo{conName=c0,conArity=n} =
	   case n of
	     0 -> rdConName cn c
	     _ -> rdParenArg (comp (rdConName cn c:replicate n rdArg))
	   where
	     c = convCon t c0
	     cn = getBaseName c0

	 rdConName cn c = rdToken (con c) (str src cn)
	 rdToken = opapp readToken
	 rdParenArg a = opapp readParenArg d a
	 rdArg = ident readArgument

	 comp = foldl1 (opapp readAp)
	 choice = foldr1 (opapp readChoice)


     return [fun src [alt (choice (map rdCon cs))]]
