module SimpPatMatchBase where
import SimpPatMatch
import Recursive(struct)
import SyntaxRec(HsExpI)
import TiBase() -- HasDef [HsDeclI i] (HsDeclI i)
import PrettyPrint2(PrintableOp)


instance (PrintableOp i, Eq i,HasSrcLoc i,ValueId i,HasIdTy n i,HasOrig i,HasOrig n)
      => SimpPatMatch i (HsExpI i) where
  simpPatMatch ids = simpPatMatchE ids . struct
