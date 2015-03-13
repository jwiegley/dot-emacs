{-+
This module defines type checking functions for generalizing inferred types
and applying context reduction (#generalise'#).
-}
module TiGeneralize where
import TiMonad
import TiTypes
import TiUtil
import TiSolve(solve,TypeConstraint(..))
import Unification(isVar)
import TiNames(ValueId,TypeVar,dictName,dictName')
import TiClasses hiding (isVar)
import TiKinds
--import TiPrelude
import TiContextReduction
import TiDefault
import TiFunDeps(predDeps,closure,improvement)
import TiFresh
import HasBaseStruct
import HsConstants(mod_Prelude,tuple)
import BaseSyntax(srcLoc,TI(..))
import TypedIds(NameSpace(..))
import PrettyPrint hiding (var)
import Data.List((\\),partition,nub)--,intersect
import MUtils

--import Debug.Trace(trace) -- debug

{-+
If there were polymorphic kinds, #kgeneralise# would produce kind schemes,
but currently it just instantiates any remaining kind variables after kind
inference to *, in accordance with the Haskell 98 report, section 4.6.
-}
kgeneralise m =
  do (kbs,s) <- getKSubst m
     return $ (map.fmap) (fixkvars . ksubst s) kbs

{-+
As #kgeneralise#, but treat Pred as equal to *. Useful for kind checking
after the dictionary translation.
-}
kgeneraliseSloppy m =
  do (kbs,s) <- getKSubstSloppy m
     return $ (map.fmap) (apFst (fixkvars . ksubst s)) kbs

--generalise1 u = generalise' u id
--generalise u = generalise' u fmap

{-+
At the moment, #checkKinds# only keeps track of the kinds of type variables
that remain after type inference. It could be improved to also check
that all subsitutions performed were kind preserving.
-}
checkKinds kpreds = return (tyvars kpreds)
  where
    --tyvars :: Unifiable i => [Kinded (Type i)] -> [Kinded i]
    tyvars kpreds = nub [v:>:k|t:>:k<-kpreds,Just v<-[isVar t]] -- hmm
{-
catchAmbiguity dicts =
    if null dicts
    then done
    else fail $ pp ("Unresolved overloading: "<+>ppDicts dicts)
-}

{-+ Iterate context reduction and improvement until nothing changes -}
reduceAndImprove dicts0 = 
  do (dicts1,r1)  <- contextReduction dicts0
     subst1@(S s) <- errorContext "Applying functional dependencies" $
                     improvement [ p | d:>:p<-dicts1]
     if null s
	then return (dicts1,r1,subst1)
	else do --trace (pp $ "Improvement:"<+>vcat [ppi s,"of"<+>ppi dicts1]) $ done
                (dicts2,r2,subst2) <- reduceAndImprove (apply subst1 dicts1)
		return (dicts2,r2 . r1,compS subst2 subst1)


{-+ Generalize inferred types: -}
generalise' keepambig unrestricted fmap' m =
  do env <- getTEnv
     (x:>:t0,res@(dicts0,kpreds0,subst0)) <- getSubst m
     --trace (pp (t0,res)) $ return ()
     ((dicts,r,subst1),([],kpreds1,S [])) <- getSubst $ reduceAndImprove dicts0
     let subst@(S s) = compS subst1 subst0
     kpreds <- checkKinds (kpreds1++[apply subst1 t:>:k|t:>:k<-kpreds0])
     --trace (pp kpreds) $ return ()
     mono <- monomorphism # getEnv -- The monomorphism restriction is optional!
     fdeps <- predDeps [ p | d:>:p<-dicts]
     let t = apply subst t0
	 ngvs0 = tv env -- could probably be made more efficient...
         s' = [s1|s1@(v,_)<-s,v `elem` ngvs0]
         -- Non-generic variables by the usual Hindley-Milner rules:
	 hmngvs0 = ngvs0++tv (map snd s')
         -- Non-generic vars when taking functional dependencies into account:
	 hmngvs = closure fdeps hmngvs0
	 -- (deferred,retained) predicates:
         (ngdicts,gdicts0) = if not mono || unrestricted
			     then partition ng dicts
			     else (dicts,[]) -- monomorphism restriction applies
	   where ng = all (`elem` hmngvs) . tv
	 mrngvs = tv ngdicts
	 ngvs = hmngvs++  -- the usual Hindley-Milner restriction
                mrngvs    -- from the monomorphism restriction
         (ngkpreds,gkpreds0) = partition ng kpreds
	   where ng (v:>:k) = v `elem` ngvs -- mrngvs is not enough!
	 --(avs,(ambigdicts,gdicts)) = ambiguities ngvs gdicts0 t
     --catchAmbiguity ambigdicts; let subst' = idS; r' = id
     (gdicts,(subst',r')) <-
       let known = (if keepambig then tdom gkpreds0 else [])++{-hm-}ngvs
       in resolveAmbiguities fdeps known gdicts0 t
     gkpreds <- checkKinds [varSubst subst' v:>:k|v:>:k<-gkpreds0]
     let ds:>:ctx = unzipTyped gdicts
         gvs = tdom gkpreds
	 ks = map (emap HsVar) gkpreds
	 gen t = Forall ags (kinded ks gs) qt
	   where ags = filter (\ (v:>:_)->v `notElem` gs) gkpreds
		 qt = ctx:=>t
		 gs = tv qt \\ ngvs -- normal type scheme
		 --gs = gvs \\ ngvs -- keep "ambiguous" type variables
         sc = fmap' gen t
     mapM_ constrain [tyvar v:=:t|(v,t)<-s'] -- deferred equality constraints
     mapM_ addinst ngdicts -- deferred predicates
     --trace (pp $ "ngkpreds:"<+>ngkpreds) $ return ()
     mapM_ addkinst [tyvar v:>:k|v:>:k<-ngkpreds] -- what to propagate?
     --abstract ds (r (apply subst x))>:fmap' gen t
     (ds,r' $ apply subst' $ r $ apply subst x)>:sc


getSubst m = do env <- getKEnv ; getSubst' (solve env) m
getKSubst = getSubst' ksolve
getKSubstSloppy = getSubst' ksolveSloppy

getSubst' solve m =
  do (ans,cs) <- getConstraints m
     subst <- solve cs
     return (ans,subst)
