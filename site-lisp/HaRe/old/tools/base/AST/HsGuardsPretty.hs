module HsGuardsPretty where

import SrcLoc1
import HsGuardsStruct
import PrettySymbols(rarrow)
import PrettyUtil(ppWhere)
import PrettyPrint

-- Pretty printing for HsAlt
instance (Printable e, Printable p, Printable ds) =>
         Printable (HsAlt e p ds) where
    ppi (HsAlt s p rhs ds) =
      sep [ppi p,nest 2 $ sep [ppRhs rarrow rhs,ppWhere (ppis ds)]]


-- added by cmb21
instance (Printable e) =>
         Printable (HsRhs e) where
   ppi r@(HsBody e) = ppRhs equals r
   ppi r@(HsGuard gs) = ppRhs equals r


--ppRhs :: Printable e => Doc -> Doc -> HsRhs e -> Doc -> Doc
ppRhs to (HsBody e)   = nest 2 $ sep [ppi to, funNest e]
ppRhs to (HsGuard gs) = vcat $ map ppGuard gs
  where ppGuard (_, guard, body) =
	  nest 2 $ sep [ '|' <+> guard <+> to, funNest body]
