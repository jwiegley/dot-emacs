module PfeDepCmds where
import Prelude hiding (print)
import Data.List(nub,intersect)
import Control.Monad(unless)

import HsName(HsName(..))
import HsIdent(getHSName)
--import HsConstants(main_name)
import SourceNames(SN(..))
import SrcLoc1(loc0,srcLoc,srcLine,srcColumn)
import PFEdeps(runPFE5,depModules',tdepModules')
import Pfe0Cmds(mainModules)
import PfeParse
import PFE0(allModules,pput,epput,getCurrentModuleGraph,getSubGraph,preparseModule)
import PFE2(getModuleExports)
import AbstractIO
import MUtils
import QualNames(getQualified)
import HasBaseName(getBaseName)
import DefinedNames(definedNames)
import UniqueNames(HasOrig(..),PN(..),Orig(..),noSrcLoc,origModule)
import PNT(PNT(..))
import TiPNT() -- instances for PNT
--import TiNames(instName)
import TypedIds(IdTy(..),idTy,NameSpace(..),namespace)
import Ents(Ent(..))
import Relations(applyRel)
import SimpleGraphs(graph,nodes,reachable,isReachable,listReachable,reverseGraph)
--import OrdGraph --slower than Graph!
import PrettyPrint

import PFE3(refsModule)
--import RefsTypes(isDef,shPos)
--import ConvRefsTypes(simplifyRefsTypes')

runPFE5Cmds ext = runCmds (runPFE5 ext)

pfeDepCmds =
    [("deps" ,        (tModuleArgs deps,
	               "compute dependency graph for definitions")),
     ("needed",       (tQualIds needed',"needed definitions")),
     ("neededmodules",(tQualIds neededmodules',
		       "names of modules containing needed definitions")),
     ("dead",         (tQualIds dead',"dead code (default: Main.main)")),
--   ("refs",         (moduleArgs refs,"list what idenfifiers refer to")),
     ("uses",         (entityId uses,"find uses of an entity"))]

tModuleArgs = moduleArgs' opts . uncurry
  where opts = (,) #@ dot <@ untyped
        dot = kwOption "-dot"

tQualIds cmd = f #@ untyped <@ many (arg "<M.x>")
  where f depM = cmd depM @@ parseQualIds

untyped = depM #@ kwOption "-untyped"
  where
    depM untyped optms = pick # depM' untyped optms
      where pick = maybe id (\ms -> filter(\ d@(m,ds)->m `elem` ms)) optms
    depM' untyped = if untyped then depModules' else tdepModules'

--needed = needed' depModules'
--tneeded = needed' tdepModules'

needed' dm qids =
  do (_,_,used) <- snd # depgraph' dm qids
     pput $ ppOrigs (listReachable used)

--neededmodules = neededmodules' depModules'
--tneededmodules = neededmodules' tdepModules'

neededmodules' dm qids =
  do (_,_,used) <- snd # depgraph' dm qids
     pput $ fsep (nub $ map origModule (listReachable used))

--dead = dead' depModules'
--tdead = dead' tdepModules'

dead' dm [] = do mains <- mainModules
                 dead'' dm [(m,"main")|m<-mains]
dead' dm qids = dead'' dm qids

dead'' dm qids =
  do (g,ids,used) <- snd # depgraph' dm qids
     let unused = [n|n<-nodes g,not (isReachable used n)]
     pput $ fsep (map ppOrig unused)

uses (optns,q@(m,n)) =
  do pnts <- definedPNTs m
     let ppq =  m<>"."<>n
     case pnts of
       [] -> fail.pp $ "No such"<+>ppns optns<>":"<+>ppq
       _ -> do let n=length pnts
               unless (n<2) $
                 epput$ ppq<+>"matches"<+>n<+>"entities, showing uses of all"
	       findUses pnts
  where
    ppns = maybe (pp "entity") ppns'
    ppns' ValueNames = pp "value"
    ppns' ClassOrTypeNames = "class or type"

    findUses pnts =
      mapM_ (usesIn pnts) . flip reachable [m] . reverseGraph . map snd
        =<< getCurrentModuleGraph

    definedPNTs =  map pnt . filter same . definedNames #. preparseModule
    same (i,ty) = getQualified (getBaseName (getHSName i)) == n
	          && maybe True (namespace ty ==) optns
    pnt (i,ty) = pnt' (getQualified # ty) m n

refs ms = mapM_ ref1 ms
  where
    ref1 = pput.ppRefs @@ refsModule
    ppRefs = vcat . map ppRef
    ppRef (_,r,os) = r<+>"at"<+>srcLoc r<>":" $$
		     nest 4 (vcat [pp (srcLoc o)|(o,_)<-os])

usesIn pnts m =
  do refs <- refsModule m
     let qs = sp pnts
         uses = [ppLineCol (srcLoc r)|(_,r,origs)<-refs,
                               --not (isDef r),
			       let os = sp (origs2PNT origs),
		               os `intersects` qs]
     unless (null uses) $ pput (m<>":"<+>fsep uses)
  where
    sp xs = [(x,namespace (idTy x))|x<-xs]
    origs2PNT origs =
      [PNT (getHSName pn) ty noSrcLoc|(pn,ty)<-origs]

ppLineCol p = srcLine p<>","<>srcColumn p

intersects xs ys = not . null $ intersect xs ys

depgraph = depgraph' depModules'
tdepgraph = depgraph' tdepModules'

depgraph' depModules' qids =
  do let ms = nub (map fst qids)
     deps <- depModules' . Just . map (fst.snd) =<< getSubGraph (Just ms)
     ids <- concatMapM origpnt qids
     let g = depGraph [(n,ns)|(m,(t,ds))<-deps,(ns1,(ns,h))<-ds,n<-ns1]
         always = [n|(m,(t,ds))<-deps,([],(ns,h))<-ds,n<-ns]
	 used = reachable g (nub (ids++always))
     return (deps,(g,ids,used))

depGraph = graph . mapSnd concat . collectByFst
                           -- because of names from typesigs...

origpnt (m,n) =
  do (t,rel) <- getModuleExports m
     return $ case map ent2pnt (applyRel rel (SN n loc0)) of
                [] -> [pnt m n]
                ns -> ns
  where
    ent2pnt (Ent m i ty) = pnt' ty m n
      where SN n _ = getHSName i
    pnt = pnt' Value

pnt' ty m n = PNT (PN (Qual m n) (g m n)) (conv # ty) noSrcLoc
  where
    conv (SN n s) = PN n (S s)
    g m n = G m n noSrcLoc

--dotdeps depM = pput.pdotdeps @@ depM . just
--tdotdeps = pput.pdotdeps @@ tdepModules' . just

pdotdeps deps =
    "digraph DepGraph"$$
    braces ("size=\"7.5,10.5\";ratio=fill;"$$
            vcat [p d<>"->"<>braces (fsep [p f<>";"|f<-fs])
                  |(m,(t,mdeps))<-deps,(ds,(fs,h))<-mdeps,d<-ds])
  where
    p = doubleQuotes . ppOrig

--tdeps = pput.vcat.map pdeps @@ tdepModules' . just

deps dot depM = pput.fmt @@ depM . just
  where
    fmt = if dot then pdotdeps else vcat.map pdeps

    pdeps  (m,(t,deps)) =
      sep ["module"<+>m<>":",nest 2 (vcat $ map pdep deps)]
      where
	pdep (ds,(fs,h)) = sep [fsep ds <> ":",nest 2 (fsep (map ppOrig fs))]
	ppOrig = ppOrig' (Just m)

ppOrig = ppOrig' Nothing

ppOrig' optm n =
    if Just m'==optm then ppi x else m'<>"."<>x
  where
    (m',x) = origId n

origId n =
    case orig n of
      G m' n' _ -> (m', n')
--    I m' loc  -> (m',instName m' loc)
      _ -> error ("Bug: PfeDepCmds.origId "++show n)

ppOrigs qs = vcat [m<>":"<+>fsep xs|(m,xs)<-collectByFst (map origId qs)]
