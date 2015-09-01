-- $Id: HsGuardsMaps.hs,v 1.7 2001/10/17 19:59:29 diatchki Exp $

module HsGuardsMaps where

import HsGuardsStruct
import AccList(accList)
import MUtils

mapAlt ef pf df (HsAlt s p rhs ds) = HsAlt s (pf p) (mapRhs ef rhs) (df ds)

mapRhs ef (HsBody x)   = HsBody (ef x)
mapRhs ef (HsGuard zs) = HsGuard (map (\(s, x, y) -> (s, ef x, ef y)) zs)


accAlt ef pf df (HsAlt s p rhs ds) = pf p . accRhs ef rhs . df ds

accRhs ef (HsBody x)    = ef x 
accRhs ef (HsGuard zs)  = accList (\(s, x, y)-> ef x . ef y) zs 

seqAlt (HsAlt s p rhs ds) = HsAlt s # p <# seqRhs rhs <# ds

seqRhs (HsBody x)   = HsBody # x
seqRhs (HsGuard zs) = HsGuard # mapM (\(s, x, y) -> (,,) s # x <# y) zs
