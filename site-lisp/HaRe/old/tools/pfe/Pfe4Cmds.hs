module Pfe4Cmds where

import PfeParse(runCmds,moduleArgs,moduleArgs',just,qualIds,( #@ ),(<@),
		kwOption)
import Pfe3Cmds(pfe3Cmds)

import PFE0(pput,epput)
import PFE2(getExports)
import PFE4(runPFE4,topTypes,typeCheck,rewriteAndTypeCheck,modEnv)
import PFE_Rewrites
import Ents(Ent(..))
import QualNames(mkUnqual,unqual)
import Relations(relToList)
import TypedIds(isValue,IdTy(MethodOf),owner,belongsTo,idTy)
import TI(Typing(..),TypeInfo(..),tdom,envFrom,topVal,topType,ppKinded)
import TiInstanceDB(InstEntry(..))
import HasBaseName(getBaseName)
import HsIdent(HsIdentI(..),accHsIdent2,getHSName,mapHsIdent)
import SrcLoc1(srcLoc)
import UniqueNames(orig,Orig(G),noSrcLoc)
import MUtils(( # ),( <# ),apBoth)
import PrettyPrint
import PrettySymbols hiding (not)
import PrettyUtil(ppContext,ppWhere)
import Products((><))
import OpTypes(cmpBy)
import Data.List(partition,sortBy)

{-+
The type checker can return different types, so to avoid an ambiguity when
the result is used only for pretty printing, the function tcOutput can be passed
in to restrict the result type.
-}

pfe4 ext tcOutput = runPFE4Cmds ext (pfe4Cmds tcOutput)

runPFE4Cmds ext = runCmds (runPFE4 ext)

pfe4Cmds tcOutput=
    pfe3Cmds ++
    [("tc",       (tcmd tcrw,     "type check and display decorated modules")),
     ("types",    (tcmd0 types,    "show types/kinds of top-level entities")),
     ("typeof",   (tqcmd typeof,  "show types of named top-level entities")),
     ("kindof",   (tqcmd kindof,  "show kinds of named top-level entities")),
     ("instances",(tcmd0 instances,"list instances defined in a module")),
     ("iface",    (tcmd0 ppIfaces, "show the interfaces of modules")),
     ("usedtypes",(tcmd0 utypes,   "show what types identifers are used at"))]
  where
    tcmd0 f = moduleArgs (f tcOutput)
    tcmd f = moduleArgs' rwopts (f tcOutput)
    tqcmd f = qualIds (f tcOutput)

    rwopts = o pmRewrite ## o pbRewrite ## o lcRewrite

    o rw@(Rewrite n _) = (\ b -> if b then rw else idRw) # kwOption ('-':n)
    rw1 ## rw2 = compRw #@ rw1 <@ rw2

instances tcOutput ms =
  do pfe4info <- tcOutput # topTypes (Just ms)
     pput.vcat $ [ppContext ps<+>p |(m,(_,(_,(insts,_))))<-pfe4info,
		                    m `elem` ms,
		                    (p,IE _ _ ps)<-insts]

types tcOutput ms =
  do pfe4info <- tcOutput # topTypes (Just ms)
     pput.vcat $ [map (fmap fst) ks$$ts |(m,(_,(_,(_,(ks,ts)))))<-pfe4info,
		                    m `elem` ms]

typeof tcOutput qids =
  do pfe4info <- tcOutput # topTypes (Just (map fst qids))
     mapM_ (typeof1 pfe4info) qids
{-
typeof1 pfe4info (m,s) = pput (vcat bs)
  where
    q=topVal m s
    bs = [b|(m',(_,(_,(_,(ks,ts)))))<-pfe4info,
		m'==m,
		b@(x:>:_)<-ts,
		getHSName x==q]
-}
kindof tcOutput qids =
  do pfe4info <- tcOutput # topTypes (Just (map fst qids))
     mapM_ (kindof1 pfe4info) qids
{-
kindof1 pfe4info (m,s) = pput (vcat bs)
  where
    q=topType m s
    bs = [fmap fst b|(m',(_,(_,(_,(ks,ts)))))<-pfe4info,
		     m'==m,
		     b@(x:>:_)<-ks,
		     getHSName x==q]
-}
typeof1 = info1 snd id
kindof1 = info1 fst fst

info1 envsel infosel pfe4info (m,s) = pput (vcat bs)
  where
    q=topType m s
    bs = [fmap infosel b|Just env<-[modEnv pfe4info m],
		     b@(x:>:_)<-envsel env,
		     getHSName x==q]

utypes tcOutput ms =
  do pfe4info <- tcOutput # typeCheck (Just ms)
     mapM_ (utypes1' pfe4info) ms
  where
    utypes1' pfe4info mn =
        maybe (epput $ "Unknown module:"<+>mn) utypes1
		      (lookup "".fst.snd=<<lookup mn pfe4info)
      where
        utypes1 m =
          pput (mn<>":"$$
		nest 2 (vcat.map u.sortBy (cmpBy fst).map pos.snd.envFrom $ m))

        pos xt@(x:>:_) = (srcLoc x,xt)

        u (pos,x:>:(sc,optt)) =
	    sep [x<+>"at"<+>pos<+>"::",
		 nest 4 (maybe (ppi sc) ppi optt)]

tc tcOutput ms = pptc ms =<< (tcOutput # typeCheck (just ms))

pptc ms = pptc' "" ms

pptc' rname ms pfe4info =
  pput.vcat $ [tm |(m,(_,(tms,_)))<-pfe4info, m `elem` ms,(n,tm)<-tms,n==rname++"fl"]

tcrw tcOutput rw@(Rewrite rwn _) ms =
  pptc' rwn ms . tcOutput =<< rewriteAndTypeCheck rw (just ms)

ppIfaces tcOutput ms =
  do exports <- getExports (Just ms)
     pfe4info <- tcOutput # topTypes (Just ms)
     mapM_ (pput.ppIface.iface exports pfe4info) ms

moduleInterface m =
  do exports <- getExports (Just [m])
     types <- topTypes (Just [m])
     return (iface exports types m)

iface expRels pfe4info m =
    (m,((types><kinds).partition isValue.map snd.relToList.snd
        # lookup m expRels))
  where
    kinds = map (info fst id)
    types = map (info snd id)

    info envsel infosel e@(Ent m' n _) = (e,i)
      where
        Just env = conv . envsel # modEnv pfe4info m'
	i = lift n (infosel # lookup (mkUnqual(getBaseName n)) env)


    conv env = [(unqual' (getBaseName x),y)|x:>:y<-env]
    unqual' = unqual `asTypeOf` id

    lift x = maybe (error $ pp $ "Not found:"<+>x) id
      
ppIface (m,Nothing) = "Unknown module:"<+>m
ppIface (m,Just (ts,ks)) =
    kw "module"<+>modn m<>":" $$
    nest 2 (vcat (map ppTInfo ks) $$
	    "" $$
	    vcat (map ppVInfo vs))
  where
    (subs,vs) = partition isExportedSubordinate ts

    ppV = accHsIdent2 ppi con
    ppTInfo (e,(k,ti)) = ppTypeInfo e k ti
    ppVInfo (Ent m' n _,ty) = {-ppName m'-}ppV n<+>el<+>ty
    {-
    ppName m' n =
      if m'==m
      then ppi n
      else m'<>"."<>n
    -}

    isExportedValue (x:>:_) = mapHsIdent orig x `elem` values

    isExportedSubordinate (e,_) = maybe False (`elem` types) (origOwner e)

    ppTypeInfo e@(Ent m n idty) k ti =
	case ti of
          Data    -> ppData "data"
	  Newtype -> ppData "newtype"
	  Class ps aks pds allms ->
	      sep [kw "class"<+>
		   sep [ppContext ps,
			tcon n<+>hsep (map ppKinded aks)<+>ppDeps vds],
		   nest 2 $ ppWhere (map ppi visms++more)]
	    where
	      as = tdom aks
              vds = map (apBoth (map (as!!))) pds
	      (visms,hidms) = partition isExportedValue allms
	      more = if null hidms then [] else [kw "..."]
	  Synonym as t ->
              sep [kw "type"<+>tcon n<+>hsep as<+>equals,nest 4 (ppi t)]
	  Tyvar -> var n<+>el<+>k -- ??
      where
        o = ent2orig e

        ppData dkw =
	    sep [kw dkw<+>tcon n<+>el<+>k,
		 nest 2 $ ppWhere (map ppVInfo ss)]
	  where
	    ss = filter ((==Just o).origOwner.fst) subs

    ppDeps [] = empty
    ppDeps ds = kw "|"<+>ppiFSeq (map ppDep ds)
    ppDep (as,bs) = hsep as<+>rarrow<+>hsep bs

    values = map (ent2orig.fst) ts
    types = map (ent2orig.fst) ks

    ent2orig (Ent m n _) = mapHsIdent (\n->G m n noSrcLoc) (getBaseName n)

    origOwner (Ent m n idty) = fmap orig (owner idty)
      where orig t = ent2orig (Ent m (HsCon t) undefined)
