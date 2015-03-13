module StrategoCmds where
import Prelude hiding (print)
import PFE0(pput,epput,getSubGraph)
import PFE3(parseModule)
import PFE4(rewriteAndTypeCheckModule)
import PFE_Rewrites(fbRewrite,lcRewrite,flRewrite,pmRewrite,compRw,rwFun)
import HsModule(hsModDecls)
import PfeDepCmds(tdepgraph)
import PfeParse
import PfePropCmds(baseNames)
import TiClasses(filterDefs,fromDefs)
import PFEdeps(tdefinedNames,splitDecls,isDefaultDecl)
import HsIdent(getHSName)
import MapDeclMProp() -- ?
import DefinedNames(addName)
import TiPropInstances()
import TiProp() -- for PFE, instance CheckRecursion ...
import RemoveListCompProp()
import SimpPatMatchProp()
--import TiPropDecorate(TiDecls)
--import PNT(PNT)

import qualified Prop2Stratego2 as P2S
--import qualified PropDecorate2Stratego2 as Ti2S
import qualified TiProp2Stratego2 as Ti2S

import AbstractIO(print)
import MUtils(( # ),(@@),apSnd)
import Sets(mkSet,elementOf)
import PrettyPrint((<+>))

strategoCmds =
  [("stratego", (tModuleArg stratego,"translation of one module to Stratego")),
   ("strategoslice", (tQualId strategoSlice,"translate a slice to Stratego")){-,
   ("tstratego", (moduleArg tstratego,"resolve overloading and translate one module to Stratego")),
   ("tstrategoslice", (qualId tstrategoSlice,"resolve overloading and translate a slice to Stratego"))-}]


tModuleArg = moduleArg' untyped

tQualId cmd = f #@ untyped <@ arg "<M.x>"
  where f u = cmd u @@ parseQualId

untyped = kwOption "-untyped"

stratego untyped = if untyped then ustratego else tstratego
strategoSlice untyped = if untyped then ustrategoSlice else tstrategoSlice

--------------------------------------------------------------------------------

ustrategoSlice qn = slice' qn =<< transModule

ustratego m =
  do transM <- transModule
     (print.transM.hsModDecls . snd) =<< parseModule m

transModule =
  do simplify <- rwFun $ foldr1 compRw [fbRewrite,lcRewrite,flRewrite]
     let transM = P2S.rmIgnored . P2S.transDecs . simplify . addName
     return transM


slice' q@(m,n) trans =
  do ms <- map (fst.snd) # getSubGraph (Just [m])
     (_,(_,_,used)) <- tdepgraph [q]
     let needed = mkSet used
     print.concatMap trans =<< mapM (moduleSlice needed) ms

moduleSlice needed m =
  filter (isNeeded needed m) . splitDecls . hsModDecls . snd # parseModule m

--------------------------------------------------------------------------------

tstrategoSlice qn = tslice' qn ttransM

ttransM = P2S.rmIgnored . Ti2S.transDecs' -- . addName

tstratego m =
    print.ttransM.fromDefs.hsModDecls =<< rewriteAndTypeCheckModule rewrite m

tslice' q@(m,n) trans =
  do ms <- map (fst.snd) # getSubGraph (Just [m])
     (_,(_,_,used)) <- tdepgraph [q]
     let needed = mkSet used
     print.concatMap trans =<< mapM (tmoduleSlice needed) ms

tmoduleSlice needed m =
    filter (isNeeded needed m) . splitDecls . fromDefs . hsModDecls
      # rewriteAndTypeCheckModule rewrite m
--  where
--    t = id :: TiDecls PNT -> TiDecls PNT

--------------------------------------------------------------------------------

rewrite = pmRewrite `compRw` lcRewrite

isNeeded needed m d = isDefaultDecl d || isNeeded' d
  where
    isNeeded' =
        any (`elementOf` needed) . map getHSName . tdefinedNames False m
