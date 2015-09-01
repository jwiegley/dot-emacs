module HsIdentPretty where
import PrettyPrint
import HsIdent

instance Printable i => Printable (HsIdentI i) where
    ppi   = ppi   . getHSName
    wrap  = wrap  . getHSName

instance PrintableOp i => PrintableOp (HsIdentI i) where
    isOp = isOp . getHSName
    ppiOp = ppiOp . getHSName


ppcon pp = accHsIdent2 (var.pp) (con.pp) -- ppcon is a misleading name...
ppconop pp = accHsIdent2 (varop.pp) (conop.pp) -- ppconop is a misleading name...
