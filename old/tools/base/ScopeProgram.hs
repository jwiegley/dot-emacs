module ScopeProgram(scopeProgram,scopeProgram',PNT(..)) where

import ScopeModule
import PNT(PNT(..))
import PrettyPrint
import OutputM
import HsModule(hsModName)

scopeProgram (mss0,wms) =
    if null errors
    then return (mss,wms)
    else fail (pp $ vcat errors)
  where
    (mss,mrefs) = scopeProgram' (mss0,wms)

    errors = [m<>": "<>msg | (m,refs)<-mrefs, (sp,i,os)<-refs, msg<-err i os]

    err i [] = [not_in_scope i]
    err i [o] = []
    err i os = [ambiguous i os]

    not_in_scope i = "Not in scope: "<>i
    ambiguous i os = "Ambiguous: "<>i<>": "<>os


scopeProgram' (mss,wms) = listOutput $ mapM (mapM scopeMod) mss
  where
    -- Hmm. scopeModule outputs exactly one element
    scopeMod mod = p (scopeModule wm mod)
      where
        Just wm = lookup m wms
        m = hsModName mod
	p (x,refs) = output (m,refs) >> return x
