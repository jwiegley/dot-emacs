-- Pretty printing for the K functor --

module HsKindPretty where

import PrettyPrint
import HsKindStruct
import PrettySymbols

instance Printable x => Printable (K x) where
    ppi (Kfun k1 k2) = wrap k1 <> rarrow <> k2
    ppi k            = wrap k

    wrap Kstar = star
    wrap Kpred = moon
    wrap Kprop = kw "P"
    wrap k     = parens (ppi k)   
