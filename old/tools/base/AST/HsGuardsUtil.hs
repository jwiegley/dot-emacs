module HsGuardsUtil() where

import SrcLoc1
import HsGuardsStruct

instance HasSrcLoc (HsAlt e p ds) where
    srcLoc (HsAlt s _ _ _) = s


