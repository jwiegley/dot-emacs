{-+
Functions to support the implementation of functional dependencies, as described
by Mark P. Jones in "Type Classes with Functional Dependencies",
http://www.cse.ogi.edu/~mpj/pubs/fundeps.html
-}
module TiFunDeps where
import TiTypes
import HsTypeStruct
--import TiFreeNames(freeTyvars)
import TiInstanceDB(classInstances,InstEntry(..))
import TiMonad
import TiUtil(freshen)
import Unification(unify,match,subst)
import TiSolve(expandSynonyms)

import PrettyPrint
import MUtils(( # ),( #. ),(@@),collectByFst,done,usort,concatMapM,mapBoth)
import Control.Monad(unless)
import Data.Maybe(mapMaybe)
import Data.List((\\),nub)

--import Debug.Trace(trace)
----mtrace s = trace s $ done
trace x y = y

{-+
Functions to ensure that declared instances are consisent with the functional
dependencies. See section 6.1 of the paper

We have relaxed the first condition in 6.1 to take the dependencies
implied by the predicates to the left of the arrow into account, to allow 
instances like C a b => C [a] [b], where F_C = 1->2.
-}

checkInstances insts0 =
  do insts <- mapM flatInst insts0
     mapM_ checkInstanceConsistency insts
     mapM_ checkPairwiseConsistency (collectByFst insts)

-- Check that instances are pairwise consistent
checkPairwiseConsistency (cl@(HsCon c),heads) =
  do (fdeps,_) <- getDeps cl
     iheads <- instanceHeads c
     unless (null fdeps) $ mapM_ (checkDeps fdeps) (pairwise heads iheads)
  where
    checkDeps fdeps p = mapM_ (checkDep p) fdeps

    checkDep ((head1,_),(head2,_)) (dxs,rxs) = maybe done compare (unify domain)
      where
        ps = zip head1 head2
        domain = map (ps!!) dxs
        range = map (ps!!) rxs

        compare s = unless (all equal range) inconsistent
          where equal (t1,t2) = subst s t1==subst s t2

	inconsistent = 
          fail $ pp $ "Instances are not pairwise consistent w.r.t. functional dependencies:" $$
                      nest 4 (vcat [appc cl head1,appc cl head2])

-- Check that an instance is consistent with the functional dependencies:
checkInstanceConsistency (cl,(ts,ps)) =
  do (fdeps,arity) <- getDeps cl
     unless (length ts==arity) $ badInstanceHead p
     pdeps <- predDeps ps
     unless (checkDeps ts pdeps fdeps) $
       fail $ pp $ sep [ppi "Instance is more general than dependencies allow:",ppi p]
  where
    p = appc cl ts
    checkDeps ts pdeps fdeps = all (checkDep ts pdeps) fdeps

    checkDep ts pdeps (dxs,rxs) = range `isSubsetOf` closure pdeps domain
      where
	 domain = vars dxs
	 range = vars rxs
	 vars ix = tv [ts!!i|i<-ix]

-- These errors shouldn't happen for instances that are free from kind errors
badInstanceHead hd = fail $ pp $ "Malformed instance head:"<+>hd

{-+ Iterated improvement: -}
improvements ps =
  do is <- improvement ps
     if apply is ps==ps
	then return is
	else (`compS` is) # improvements (nub (apply is ps))

{-+ Compute an improving subsitution using functional dependencies
    (section 6.2): -}

improvement ps =
    S . tr #. unify @@ expand @@
    concatMapM improve . collectByFst . mapMaybe flatPred $ ps
  where
    expand eqns =
       do kenv <- getKEnv
	  return $ mapBoth (expandSynonyms kenv) eqns

    tr [] = []
    tr s = trace ("Improving subst="++pp s) s

    improve (cl@(HsCon c),heads) =
      do (fdeps,_) <- getDeps cl
         iheads <- map fst # instanceHeads c
	 let imps = concatMap (improveAll cl heads iheads) fdeps
	 concatMapM freshimp imps

    freshimp ([],eqns) = return eqns -- optimization
    freshimp (gs,eqns) = freshen gs eqns

    improveAll cl heads iheads (dxs,rxs) =
        map improvePair (pairs1 heads) ++ map improveInst (pairs2 iheads heads)
      where
	improvePair (head1,head2) =
	  if ds1==ds2
	  then trace ("Improving pair "++show (dxs,rxs)++" "++ppp (head1,head2)) $
               ([],[(head1!!rx,head2!!rx)|rx<-rxs])
	  else ([],[])
          where (ds1,ds2) = ([head1!!dx|dx<-dxs],[head2!!dx|dx<-dxs])

        improveInst (ihead,head) =
            maybe ([],[]) improve1 $ match [(ihead!!dx,head!!dx)|dx<-dxs]
          where
	    improve1 s =
                trace ("Improving inst "++show (dxs,rxs)++ppp (ihead,head)) $
                (tv eqns \\ tv head,eqns)
              where eqns = [(subst s (ihead!!rx),head!!rx)|rx<-rxs]
        ppp (h1,h2) = pp (appc cl h1,appc cl h2)

{-+ Computing the closure w.r.t functional dependencies
    (section 5.2 of the paper).
-}
closure fdeps = fix step . usort
  where
     step xs = usort (xs++[r|(ds,rs)<-fdeps,ds `isSubsetOf` xs,r<-rs])
     fix f = stop . iterate f
     stop (x1:x2:xs) = if x1==x2 then x1 else stop (x2:xs)

{-+ Computing the functional dependencies applied by a set of predicates
    (section 6.3)
-}
predDeps ps = concatMapM pred1Deps (mapMaybe flatPred ps)
pred1Deps (cl,ts) = 
  do (fdeps,_) <- getDeps cl
     let vars ix = tv [ts!!i|i<-ix]
     return [(dvs,rvs)|(dxs,rxs)<-fdeps,
	               let dvs = vars dxs
	                   rvs = vars rxs,
	               not (null rvs)]

{-+ Looking up the functional dependencies (and the arity) for a class: -}
getDeps cl =
  do (k,Class _ ps fdeps _) <- env kenv cl
     return (fdeps,length ps)

{-+ Looking up all the instances of a given class: -}
instanceHeads c = map snd # (mapM flatInst . flip classInstances c =<< getIEnv)

{-+
Auxiliary functions
-}

xs `isSubsetOf` ys = (`elem` ys) `all` xs

pairwise hs hs' = pairs1 hs++pairs2 hs hs'

pairs1 []     = []
pairs1 (x:xs) = [(x,x')|x'<-xs]++pairs1 xs

pairs2 xs ys = [(x,y)|x<-xs,y<-ys]

flatInst (hd,IE _ _ ps) =
  do (cl,hd') <- flatPred hd
     return (cl,(hd',ps))

flatPred ty = maybe (badInstanceHead ty) return (flatConAppT ty)

appc cl ts = appT (ty cl:ts)
