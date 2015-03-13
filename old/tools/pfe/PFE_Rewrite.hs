{-# OPTIONS -fglasgow-exts #-}
{-# LANGUAGE MultiParamTypeClasses, OverlappingInstances, UndecidableInstances, FunctionalDependencies, NoMonomorphismRestriction #-}
{-+
Sometimes we need to apply some rewrites before type checking,
but we need to record what rewrite was applied so that cached results
with different rewrites can be kept apart. Rewrites are therefore paired
with names that uniquely identify them.
-}
module PFE_Rewrite where
import MUtils

type RewriteName = String
data Rewrite m ds = Rewrite {rwName::RewriteName, rwFun::m (ds->ds)}

idRw = Rewrite "" (return id)
compRw (Rewrite n1 m1) (Rewrite n2 m2) = Rewrite (n1++n2) ((.) # m1 <# m2)
-- Note: composing with idRw doesn't change the name of the rewrite

