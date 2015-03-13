module SimpPatMatchProp where
import SimpPatMatch
import Recursive(struct)
import PropSyntaxRec(HsExpI)
--import PropSyntaxStruct(prop)
import TiProp() -- HasDef [HsDeclI i] (HsDeclI i)
import PrettyPrint(PrintableOp)

instance (Eq i,PrintableOp i,
          HasSrcLoc i,ValueId i,HasIdTy n i,HasOrig i,HasOrig n)
      => SimpPatMatch i (HsExpI i) where
  simpPatMatch ids = simpPatMatchE ids . struct
