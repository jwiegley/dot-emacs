{-+
Reusable functions for translation from the (non-recursive) P-Logic structure
to Stratego.
-}

module PropStruct2Stratego where
import StrategoAST
import HsPropStruct
import HsPropMaps
import PrettyPrint(pp)

transPD trId trPA trPP pd =
  case mapPD trId trPA trPP pd of
    _ -> error ("not yet: "++pp pd)

transPA trId trE trT trPA trPP pa =
  case mapPA trId trE trT trPA trPP pa of
    _ -> error ("not yet: "++pp pa)

transPP trId trE trP trT trPA trPP pred =
  case mapPP trId trE trP trT trPA trPP pred of
    _ -> error ("not yet: "++pp pred)
