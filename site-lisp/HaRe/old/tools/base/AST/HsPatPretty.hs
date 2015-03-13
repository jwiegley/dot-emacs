--- Pretty printing for the P functor

module HsPatPretty () where

import HsPatStruct
import HsIdentPretty
import HsFieldsPretty()
import HsLiteralPretty()
import PrettyPrint

instance (PrintableOp i,Printable p) => Printable (PI i p) where
  ppi (HsPId n)            = ppcon wrap n
  ppi (HsPLit s l)         = lit l
  ppi (HsPNeg s l)         = kw "-" <> lit l
  ppi (HsPSucc s n l)      = parenBinOp n (kw "+") l
  ppi (HsPInfixApp x op y) = parenBinOp x (conop (ppiOp op)) y
  ppi (HsPApp n ps)        = con (wrap n) <+> (fsep $ map wrap ps)
  ppi (HsPTuple s ps)      = ppiFTuple ps
  ppi (HsPList  s ps)      = ppiList ps
  ppi (HsPParen p)         = wrap p
  ppi (HsPRec n fs)        = con (wrap n) <> braces fs
  ppi (HsPAsPat n p)       = wrap n <> kw "@" <> wrap p
  ppi (HsPWildCard)        = kw '_'
  ppi (HsPIrrPat p)        = kw "~" <> wrap p

  wrap p =
    case p of
      HsPId n       -> ppcon wrap n
      HsPLit s l    -> lit l
      HsPApp n []   -> con (wrap n)
      HsPTuple s ps -> ppi p
      HsPList  s ps -> ppi p
      HsPParen p    -> parens p
      HsPAsPat n _  -> ppi p
      HsPWildCard   -> kw '_'
      HsPInfixApp{} -> ppi p
      HsPSucc{}     -> ppi p
      _             -> parens p
