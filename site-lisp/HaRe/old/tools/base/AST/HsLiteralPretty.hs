module HsLiteralPretty where
import HsLiteral
import PrettyPrint

instance Printable HsLiteral where
    ppi	(HsInt i)        = ppi i
    ppi	(HsChar c)       = ppi (show c) --litChar c
    ppi	(HsString s)     = ppi (show s) --litString s
    ppi	(HsFrac r)       = ppi r
    -- GHC unboxed literals:
    ppi (HsCharPrim c)   = show c                  <> '#'
    ppi (HsStringPrim s) = show s                  <> '#'
    ppi (HsIntPrim i)    = ppi i                   <> '#'
    ppi (HsFloatPrim r)  = float  (fromRational r) <> '#'
    ppi (HsDoublePrim r) = double (fromRational r) <> "##"
    -- GHC extension:
    ppi (HsLitLit s)     = doubleQuotes s

    wrap = ppi
