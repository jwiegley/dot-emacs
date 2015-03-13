module SrcLocPretty where
import SrcLoc1
import PrettyPrint

instance Printable SrcLoc where
    ppi (SrcLoc f _ l c) =  f<>":"<>l<>','<>c
    wrap = ppi

shLineCol (SrcLoc _ _ l c) = show l++"_"++show c
