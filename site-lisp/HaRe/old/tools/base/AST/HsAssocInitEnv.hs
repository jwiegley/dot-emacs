module HsAssocInitEnv where
import HsAssoc
import HsName

-- Fixities for an ad hoc selection of operators from the Prelude, for testing.
initEnv =
    foldl extend emptyOE
      [l 6 "+",
       l 7 "*",
       l 6 "-",
       r 0 "$",
       r 5 ":",
       r 5 "++",
       n 6 ":+"]
    where
      nm s = UnQual s
      i a p n = (nm n,HsFixity a p)
      l = i HsAssocLeft
      r = i HsAssocRight
      n = i HsAssocNone
