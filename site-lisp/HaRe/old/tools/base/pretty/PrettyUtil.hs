module PrettyUtil (ppWhere,ppContext) where

--import SrcLoc
import PrettyPrint
import PrettySymbols(imp)


-- Pretty prints where declaration lists, also used in multiple places.
--ppWhere :: [Doc] -> Doc
ppWhere [] = empty
ppWhere ds = sep [kw "where",letNest (layout ds)]

-- Pretty prints contexts, if they are present
ppContext []  = empty
ppContext [c] = c <+> imp
ppContext cs  = ppiFTuple cs <+> imp

