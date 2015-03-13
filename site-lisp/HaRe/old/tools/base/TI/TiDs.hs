-- Type checking sequences of declarations
module TiDs where
import Data.List(nub,(\\),intersect,partition)
import Data.Maybe(mapMaybe,fromMaybe)

import HasBaseStruct(HasBaseStruct(..),GetBaseStruct(..))
import SrcLoc1(SrcLoc,HasSrcLoc(..))
import HsLiteral(HsLiteral)
import HsDeclStruct
import HsPatStruct(PI)
import TI hiding (Subst)
import TiNameMaps
import TiDkc(Dinst,Einst)
import TiSolve
import TiSCC(sccD)
import TiContextReduction(contextReduction,entails)
import TiInstanceDB(instType,addInstKind)
import TiDerivedInstances
import TiFunDeps(checkInstances)
import Substitute
import SubstituteBaseStruct
--import QualNames

import MUtils(( # ))
import PrettyPrint(Printable,pp,vcat)

instance DeclInfo i d => DeclInfo i [d] where
  explicitlyTyped ks kinfo ctx ds = (concat kss,concat tss)
    where (kss,tss) = unzip $ map (explicitlyTyped ks kinfo ctx) ds

---
instance (
 TypeId i,ValueId i,Printable i, Fresh i,HasSrcLoc i,
 TypedId PId i,CheckRecursion i d,
 DeclInfo i d, FreeNames i d, TypeCheckDecl i d ds2,HasSrcLoc d,
 HasCoreSyntax i p,HasCoreSyntax i e,HasDef ds d,
 --HasLit e,HasLit p,
 HasBaseStruct e (Einst i e p ds),HasBaseStruct p (PI i p),
 DefinedNames i d,AccNames i d,
 HasBaseStruct d (Dinst i e p ds), GetBaseStruct d (Dinst i e p ds),
 HasDef ds2 d2,  HasLocalDef i e2 d2,  Types i d2,
 HasAbstr i ds2, HasLocalDef i e2 ds2, Types i ds2, AddDeclsType i ds2,
 HasCoreSyntax i e2,
 MapExp e2 ds2,Subst i e2,HasTypeApp i e2, -- for dicts in mono rec calls
 KindCheck i d ()) => TypeCheckDecls i [d] ds2
  where
    tcTopDecls rewrite ds = decorate # tcDs rewrite True ds
    tcInstDecls mts ds = do ds':>:bs <- tcExplDs mts ds
			    return (addDeclsType ([],bs) ds')

--}

decorate (ds:>:(insts,dt)) = addDeclsType dt ds:>:(insts,dt)

--sccD ds = [ds] -- dummy

-- How to type check a (possibly recursive) group of declarations:
tcDs rewrite r ds0 =
    do -- Recursive type synonyms and suprtclass relations can cause the type
       -- checker to loop, so start by checking...
       checkRecursion ds0
       -- Infer the kinds of all class/type identifers, including
       -- type variables.
       -- (Names are assumed to have been made unique in an earlier pass.)
       ks <- errorContext "Kind inference" $
             kgeneralise $ do kbs <- kintro (allTypeNames ds0)
			      let kbs' = map (fmap (flip (,) undefined)) kbs
                              extendkts kbs' (kc ds0>>return kbs)
       -- Find additional info about classes and types
       -- and the types of all explicitly typed value identifiers...
       let (kinfo,expls) = explicitlyTyped ks (map (fmap snd) kinfo) [] ds0
	   vkinfo = [v:>:(k,Tyvar)|v@(HsVar _):>:k<-ks]
       expl <- mapM checkTypeSigClash (collectTyped expls)
       -- ...and add them to the environment (if in a recursive group).
       extendkts (kinfo++vkinfo) $ opt r (extendts expl) $
	do -- Extend the instance database with the declared instances
           (insts,ds) <- getInstances ks ds0
	   checkInstances insts
	   extendIEnv insts $
	    do -- Infer the types of the implicitly typed declarations,
	       -- one strongly connected component (scc) at a time...
	       let (dsImpl,dsExpl) = partition (isImplicit ns) ds
		   dsccs = sccD dsImpl
		   ns:>:_=unzipTyped expl
	       ds1:>:bs1 <- tcImplBGs r expl dsccs
	       -- ...and add them to the environment (if in a recursive group)
	       opt r (extendts bs1) $
		do -- Infer the types of the explicitly typed declarations
		   -- and check that they agree with their explicit types
		   ds2:>:bs2 <- tcExplDs expl dsExpl
		   let env = (kinfo,its++filter noDup bs0++expl)
		       its=map instType insts
		       bs0 = bs1++bs2
		       noDup (x:>:_) = x `notElem` ns
		   -- Finally, return the translated declarations, the
		   -- instances, and the resulting environment
		   ((ds1 `appendDef` ds2)>:(insts,env))
  where	
    getInstances ks ds =
        do modmap <- getModule
           kenv <- getKEnv
           let insts1 = map (addInstKind ks) (instDecls ds modmap kenv)
	   extendIEnv insts1 $
	    do stdnames <- getStdNames
	       (insts2,ds2) <- unzip # derivedInstances ks stdnames modmap kenv ds
	       let insts = insts1++map (addInstKind ks) insts2
	       return (insts,ds++rewrite ds2)

    instDecls ds modmap env =
         [instDecl s optn ctx tp|HsInstDecl s optn ctx tp _<-mapMaybe basestruct ds]
       where
        instDecl s optn ctx tp = (syn tp,(n,map syn ctx))
	  where n = fromMaybe (instName' modmap s tp) optn
        syn = expandSynonyms env

    isImplicit ns d = any (`notElem` ns) (definedValueNames d)

-- Type check a sequence of implicitly typed binding groups:
tcImplBGs r expl [] = noDef>:[]
tcImplBGs r expl (ds:dss) =
  do ds1:>:bs1 <- tcImplBG r expl ds
     ds2:>:bs2 <- extendts bs1 $ tcImplBGs r expl dss
     ds1 `appendDef` ds2>:bs1++bs2

tcImplBG r expl ds =
    checkExplicit r (srcLoc ds) expl =<< tcBG expl r False ds

-- Type check declarations with explicit type signatures
-- pre: the explicitly given types have already been added to the environment
tcExplDs expl ds =conc . unzipTyped # mapM (tcExplD expl) ds
  where conc (dss:>:bss) = concatDefs dss:>:concat bss

tcExplD expl d =
  checkExplicit False (srcLoc d) expl =<< tcBG expl False True [d]

-- Typecheck one (mutually recursive) binding group:
tcBG all_ebs r isExpl ds =
  addErrorContext $
  do (dns,ds'):>:bs' <-
       generalise' keepambig unr mapTs $
       do bs1 <- tintro (values\\ens)
	  bs2 <- tintro ens
	  let bs=bs1++bs2
	      lbs = (map.fmap) mono bs1
	  (:>:bs) # opt r (extendts lbs) (mapM (tcDecl bs) ds)
     (dns,concatDefs ds')>:bs'
  where
    ens=values `intersect` all_ens where all_ens:>:_=unzipTyped all_ebs
    (types,values) = definedNamesSplit ds
    unr = all (isUnrestricted isExpl) ds
    keepambig = all keepAmbigTypes ds

    mapTs = map . fmap
      --where mapTM f (x:>:t) = (x:>:) # f t
    --typed = uncurry (:>:)

    addErrorContext =
      if null types && null values
      then posContext' (srcLoc ds) "in declaration"
      else posContext (srcLoc ds) .
           declContext (types++values)
           {-errorContext (render
	    (sep [(if unr then "In an un" else "In a ")
		   <>"restricted definition of",
		  nest 4 (fsep types $$ fsep values)]))-}

opt b f = if b then f else id

checkExplicit r loc explicit ((dns,d):>:inferred) =
    posContext' loc "type signature vs inferred type" $
    do let xs:>:_ = unzipTyped inferred
	   ixs = xs \\ exs
           (exs,eqscs) =
	       unzip [ (x,(it,et)) |x:>:it<-inferred,y:>:et<-explicit,y==x]
           pick x = if x `elem` exs
		    then head [ t |t@(y:>:_)<-explicit,x==y]
		    else head [ t |t@(y:>:_)<-inferred,x==y]
           -- abstract' adjusts monomorphic rcurive calls:
	   abstract' ixs dns d =
	       if r
	       then abstract dns (esubst addDicts d)
	       else abstract dns d
	     where
	       addDicts x = if HsVar x `elem` ixs
			    then foldl1 app (x':map var dns)
			    else if HsVar x `elem` exs
			         then x' 
				 else var x -- Grr!! Type info is lost
		 where
		   x' = spec (HsVar x) sc (map tyvar (tdom gs))
		   _:>:sc@(Forall ags gs qt) = pick (HsVar x)
       if null eqscs then abstract' ixs dns d>:map pick xs
	 else do (ids,eds,eqts) <- freshInsts dns eqscs
		 s0 <- matchEqns eqts =<< getKEnv
		 let ids' = apply s0 ids
		 id {-errorContext (eds,ids',apply s0 eqts)-} $ do
		  -- Although the context ids should already be reduced,
		  -- the instance ids' may still not be in normal form,
		  -- so we have to apply context reduction again.
		  (ids'',r1,s1) <- do reduceAndImprove ids'
		  (is,r2) <-
                    do env <- getKEnv
		       let eds' = (map.fmap) (expandSynonyms env) (apply s1 eds)
		       (eds' `entails` ids'') env
		  let edns:>:_ = unzipTyped eds
		      r = r2 . r1
		      s@(S su) = is `compS` s1 `compS` s0
		  ngvs <- tv # getTEnv
		  mapM_ constrain [tyvar v:=:t|(v,t)<-su,v `elem` ngvs]
		  abstract' ixs edns (r (apply s d))>:apply s (map pick xs)
  where
    freshInsts dns eqscs =
       do ((ctx,eds):_,eqts) <- unzip # mapM freshInst' eqscs
	  return (zipTyped (dns:>:ctx),eds,eqts)

    freshInst' (isc,esc) =
       do -- Don't freshen the inferred type, the quantified tvars can appear in the body:
          --(ids,it) <- freshInst isc
          --let _:>:ctx = unzipTyped ids
          let Forall _ _ (ictx:=>it) = isc
	      Forall _ _ (ectx:=>et) = esc
          --(eds,et) <- freshInst esc
          ds <- map dictName # freshlist (length ectx)
	  let eds = zipTyped (ds:>:ectx)
          return ((ictx,eds),(it,et))

{-+
We allow more than one type signature for the same identifier, but we
check that they are syntactically equal. In Haskell 98, its invalid to give
more then one type signature for the same identifier, even if they are
identical (H98 report, section 4.4.1).
-}
checkTypeSigClash (x:>:ts0) =
    case nub ts0 of -- Equality of type schemes. Hmm...
      [t] -> x>:t
      ts -> declContext [x] $
              errorContext "Conflicting type signatures" $
                fail $ pp (vcat ts)
