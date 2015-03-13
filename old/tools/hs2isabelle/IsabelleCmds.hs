module IsabelleCmds where
import Prelude hiding (print)
import PFE0(pput,epput,getSubGraph)
import PFE3(parseModule)
import PFE4(rewriteAndTypeCheckModule,topTypes)
import PFE_Rewrites(fbRewrite,lcRewrite,flRewrite,pmRewrite,compRw,rwFun)
import HsModule(HsModuleI(..),hsModImportsFrom)
import PfeDepCmds(tdepgraph)
import PfeParse(moduleArg,qualId)
import PfePropCmds(baseNames)
import TiClasses(filterDefs,fromDefs)
import TiSCC(sccD')
import PFEdeps(tdefinedNames,splitDecls,isDefaultDecl)
import HsIdent(getHSName)
import MapDeclMProp() -- ?
import DefinedNames(addName,definedNames)
import FreeNames(freeNames)
--import TiPropInstances()
import TiProp() -- for PFE, instance CheckRecursion ...
import TiTypes(Scheme(Forall),Typing((:>:)),Qual((:=>)))
import RemoveListCompProp()
--import TiPropDecorate(TiDecl)
--import PNT(PNT)

import qualified Prop2Isabelle as P2I
import qualified IsabelleAST as AST
--import qualified PropDecorate2Isabelle2 as Ti2S
import SimpFunBind
import RemoveListComp
import SimpFieldLabels(simpFieldLabels)

import AbstractIO(print)
import MUtils(( # ),(@@),apSnd)
import Sets(mkSet,elementOf)
import PrettyPrint((<+>),pp)

isabelleCmds =
  [("isabelle", (moduleArg isabelle,"simple translation of one module to Isabelle")),
   ("isabelleslice", (qualId isabelleSlice,"translate a slice to Isabelle"))]

isabelleSlice qn = undefined -- slice' qn =<< transModule

isabelle m =
  do simplify <- rwFun $ foldr1 compRw [lcRewrite]
     let transM = simplify . addName
     parsed <- fmap snd (parseModule m)
     Just types <- fmap (lookup m) (topTypes (Just [m]))
     let decls1 = hsModDecls parsed
         decls2 = transM decls1
         decls3 = sccD2 decls2
         decls4 = map P2I.transDecs decls3
         decls5 = map P2I.combineDecls decls4
         decls6 = P2I.addConstsDecls (typetable types) decls5
         isamod = AST.Module (header parsed) decls6
     print isamod

sccD2 ds = sccD' names ds
  where names d = (map fst (definedNames d), map fst (freeNames d))

header m = (pp (hsModName m), map pp (hsModImportsFrom m))

typetable (_,(_,(_,(_,xs)))) = map f xs
  where f (i :>: (Forall _ _ (_ :=> t))) = (pp i, P2I.transType t)

{-
use function besides hsModDecls to get module name, imports, exports
topTypes [m] returns PFE4Info
-}
{-
transModule =
  do simplify <- rwFun $ foldr1 compRw [lcRewrite]
     let transM = P2I.transDecs . simplify . addName
     return transM

slice' q@(m,n) trans =
  do ms <- map (fst.snd) # getSubGraph (Just [m])
     (_,(_,_,used)) <- tdepgraph [q]
     let needed = mkSet used
     slices <- mapM (moduleSlice needed) ms
     let defs = concatMap trans slices
         isamod = P2I.defs2module "" [] defs
     print isamod

moduleSlice needed m =
    --filter isNeeded . t . splitDecls . fromDefs . hsModDecls # rewriteAndTypeCheckModule simplify m
    filter isNeeded . splitDecls . hsModDecls . snd # parseModule m
  where
    isNeeded d = isDefaultDecl d || isNeeded' d
    isNeeded' = any (`elementOf` needed) . map getHSName . tdefinedNames False m
    --t = id :: [TiDecl PNT] -> [TiDecl PNT]
-}