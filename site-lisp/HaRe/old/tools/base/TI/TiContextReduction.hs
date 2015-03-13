module TiContextReduction(entails,contextReduction,contextReduction'') where
import TiInstanceDB
import TiClasses
import TiMonad
import TiTypes
import TiBySuper
import TiFresh
import TiFunDeps(improvements)
import TiNames(TypeId,ValueId,dictName)
import TiSCC(sccD')
import TiFreeNames(freeVars)
import TiSolve(expandSynonyms)
import TiUtil(freshen',freshvars)
import SrcLoc1
import PrettyPrint hiding (var)
import Data.List(partition,(\\))
import Control.Monad(msum,mplus)
import MUtils
import Debug.Trace(trace) -- debug
import TiPretty() -- debug

--type Ctx = [Typing QId Pred]

--contextReduction, rmByInst :: HasLocalDef e => IDB -> Ctx -> IM i (Ctx,e->e)


type Dict v = Typing v (Type v)
type Ctx v = [Dict v]

type DDefs v = [(Dict v,DExp v)] -- dictionary definitions
type DictsF v = DDefs v->DDefs v

contextReduction ds = contextReduction' True ds
contextReduction' delayIfOverlap ds =
    apSnd returnLets # contextReduction1' delayIfOverlap ds

contextReduction1 ds = contextReduction1' True ds

contextReduction1' delayIfOverlap ds =
 do idb <- getIEnv
    tenv <- getKEnv
    --trace (pp $ caller<+>"contextReduction1 tenv=" $$ nest 2 tenv) done
    contextReduction2 delayIfOverlap idb tenv ds

contextReduction2
  :: (TypeId v,ValueId v,HasSrcLoc v,Fresh v)
  => Bool -> IDB v -> KEnv v -> Ctx v -> TI v (Ctx v, DictsF v)
contextReduction2 delayIfOverlap idb env =
    rmDupCtx & rmBySuper & rmDupCtx & rmByInst delayIfOverlap env idb & rmDupCtx
  where
    (&) red1 red2 ds =
      do (ds1,r1) <- red1 ds
	 (ds2,r2) <- red2 ds1
	 return (ds2,r2 . r1)

    rmDupCtx = return . rmDupCtx'
    rmDupCtx' ds =
      case ds of
	[] -> ([],id)
	(d@(dn:>:dt):ds) ->
	   case partition (sameInstance d) ds of
	     (same,other) -> (d:ds',r')
	       where
		 r' = foldr l r same
		 l d' = (letvar' d' dne .)
		 dne = var dn
	    	 (ds',r) = rmDupCtx' other

    rmBySuper ds =
      do let addSuper (dn:>:dt) = tail # bySuper env (var dn:>:dt)
         supds <- concatMapM addSuper ds
	 let rm ds1 r [] = (reverse ds1,r)
	     rm ds1 r (d:ds2) =
		 case filter (sameInstance d) supds of
		   [] -> rm (d:ds1) r ds2
		   (supde:>:_):_ -> rm ds1 r' ds2
		     where r' = letvar' d supde . r
	 return (rm [] id ds)

superClosure eds env = concatMapM (bySuper env) (map (emap var) eds)

entails eds ids env = 
    do availds <- superClosure eds env
       is <- let _:>:ectx = unzipTyped availds
	         _:>:ictx = unzipTyped ids
             in improvements (ectx++ictx) -- need to skolemize vars in ectx?
       let availds' = apply is availds
	   ids' = apply is ids
	   _:>:actx = unzipTyped availds'
       r <- errorContext ("Given context:"<+>ectx $$
			  "Should entail:"<+>ictx $$
			  "Improving substitution:"<+>is) $
	    returnLets . foldr (.) id # entails' availds' env ids'
       return (is,r)
{-
    `mplus` fail (pp $ fsep [ppi "contexts don't match:",
			     ppiFTuple ectx,ppi "vs",ppiFTuple ictx])
-}
  where
    _:>:ectx = unzipTyped eds
    _:>:ictx = unzipTyped ids

entails' availds env = mapM entails0
  where
    entails0 d@(_:>:dt) =
        entails1 d `mplus` (fail $ pp $ "Can not justify:"<+>dt)

    entails1 d@(_:>:dt) =
       case filter (sameInstance d) availds of
         [] -> msum . map entails2 =<< reduceInstOneStep d
	 (supde:>:_):_ -> return (letvar' d supde)

    reduceInstOneStep d@(dn:>:inst) =
      do idb <- getIEnv
	 mapM (use1Inst d) (findInst' False idb (expandSynonyms env inst))

    entails2 (ids2,r) = foldr (.) r # mapM entails1 ids2
    
sameInstance (_:>:t1) (_:>:t2) = t1==t2


rmByInst delayIfOverlap env idb ds =
  --stpp ds $
  case ds of
    [] -> return ([],id)
    (d@(dn:>:inst):ds) ->
      case findInst' delayIfOverlap idb (expandSynonyms env inst) of
	[] -> {-(if null (tv inst)
	       then trace (pp $ fsep [ppi (srcLoc dn)<>":",
				      ppi "No instance: ",
				      ppi inst{-,
				      ppi "in",
				      ppi idb-}])
	       else id) $-}
	      preserve
	[i] -> if True -- null (tv inst) -- delay reduction, ...
               then useInst i
	       else trace (pp $ "Delaying"<+>d<+>srcLoc dn) $
                    preserve -- ... experiment for overlapping instances
	is -> trace msg preserve -- experiment
	      --fail msg -- normal
          where msg = pp $ sep [ppi "Ambiguous instances", "("<>map fst is<>")",
		                "for"<+>inst]
      where
        preserve = apFst (d:) # rmByInst delayIfOverlap env idb ds

	useInst inst =
            do (ids,r1) <- use1Inst d inst
	       (ds2,r2) <- rmByInst delayIfOverlap env idb (ids++ds)
	       return (ds2,r2 . r1)

use1Inst d ((idn,ips0),((gs,ip),s)) =
    do idns <- map dictName # freshlist (length ips0)
       let lgs = [g|g@(v:>:_)<-gs,v `elem` d]
             where d = tv ips0 \\ tv ip
       lvs <- freshvars lgs
       (ips,ts0) <- return $ freshen' lvs (tdom lgs) (ips0,map tyvar (tdom gs))
       let dt = funT (ips++[ip])
           ids = zipWith (:>:) idns ips
	   --Forall gs _ = sc
	   sc = mono dt -- fake, ok since it isn't used
	   ts = apply s ts0
	   --idne = var idn -- without type annotations
	   idne = DSpec (HsVar idn) sc ts -- with type annotations
	   d' = foldl1 DApp (idne:map var idns)
	   r1 = letvar' d d'
       --trace (pp ((s,gs,ips0:=>ip),(lgs,lvs,ips:=>ip))) $ done
       return (ids,r1)

letvar' v e = ((v,e):)

-- Sort dictionary definitions in dependency order and return a nested let.
returnLets r = \s -> foldr (uncurry letvar . apSnd dconv) s (order (r []))
  where
    order = concat . sccD' names
    names (d:>:_,e) = ([HsVar d],dfree e)

--------------------------------------------------------------------------------

-- To avoid an ambiguity when you only want the resulting predicates and
-- not the dictionary rewriting function:

contextReduction'' ds = fst # contextReduction1 ds

data DExp i
  = DId (HsIdentI i)
  | DApp (DExp i) (DExp i)
  | DSpec (HsIdentI i) (Scheme i) [Type i]

dconv de =
  case de of
    DId i -> ident i
    DApp e1 e2 -> app (dconv e1) (dconv e2)
    DSpec i sc t -> spec i sc t

instance HasId i (DExp i) where ident = DId
instance HasCoreSyntax i (DExp i) where app = DApp -- ; ...
instance HasTypeApp i (DExp i) where spec = DSpec

dfree de =
    case de of
      DId   i     -> [i]
      DSpec i _ _ -> [i]
      DApp  e1 e2 -> dfree e1++dfree e2
