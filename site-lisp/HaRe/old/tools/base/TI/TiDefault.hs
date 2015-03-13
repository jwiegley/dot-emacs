module TiDefault where
import TiTypes
import TiMonad
import TiContextReduction
import TiSolve(expandSynonyms)
import TiFunDeps(closure)
import SrcLoc1
import Lists(partition,(\\\),nubBy)
import OpTypes(eqBy)
import MUtils
import PrettyPrint
import Control.Monad(msum,unless)

resolveToplevelAmbiguities ps = resolveAmbiguities' (tv ps) ps
 
resolveAmbiguities fdeps ngvs ps ts =
    (,) unambigps # resolveAmbiguities' avs ambigps
  where (avs,(ambigps,unambigps)) = ambiguities fdeps ngvs ps ts

--ambiguities :: (Types v p,Types v (f (Type v))) => [v] -> [p] -> f (Type v) -> ([v],([p],[p]))

-- Partition predicates into ambiguous and unambiguous predicates:
ambiguities fdeps ngvs ps ts = (avs,partition (any (`elem` avs).tv) ps)
  where
    avs = tv (tmap ambigvs ts) -- ambiguous variables
    pvs = tv ps -- restricted variables

    ambigvs t = tyvarsAsType (pvs\\\known)
         where known=closure fdeps (tv t)++ngvs -- "known" variables
     -- Note: with functional dependencies, variables in pvs that are
     -- determined (by variables in tv t or ngvs), should also be regarded
     -- as "known"

    -- A hack to represent a set of tyvars as a type
    -- (and later get the set back with tv):
    tyvarsAsType = tupleT . map tyvar

resolveAmbiguities' avs ps =
    do let ambigs = [(av,[ p | p<-ps,av `elem` tv p])|av<-avs]
       dss <- getDefaults
       s <- S # mapM (solveAlternatives dss) ambigs
       (ds,r) <- contextReduction (apply s ps)
       unless (null ds) $
         errorContext' "Overloading" [(ppi p,srcLoc d)|d:>:p<-ds] $
         fail "Unresolved"
       return (s,r)
  where
    -- We allow multiple, possibly conflicting, default declarations,
    -- and report an error only if they produce different results.
    solveAlternatives dss ambig =
	errorContext' "Failed to resolve ambiguous overloading:"
		      [(ppi p,srcLoc d)|d:>:p<-snd ambig] $
	do env <- getKEnv
	   checkConflict env =<< mapM (solve1 ambig) dss
      where
	checkConflict env solutions =
	    case nubBy eq solutions of
	      [Just solution] -> return solution
	      [Nothing]       -> fail "Found no suitable default"
	      []              -> if null dss
				 then fail "Hmm. No defaults available?" -- bug!
				 else fail.pp $ "Hmm."<+>dss --serious bug!
	      _               -> fail "Conflicting default declarations"
	  where
	    syn = expandSynonyms env
	    eq = eqBy (fmap (syn.snd))

    solve1 ambig ds = msum # mapM (try1 ambig) ds
      where  
	try1 (v,ps) t =
	  do ds <- contextReduction'' (apply (v+->t) ps)
	     return $ if null ds
		      then Just (v,t)
		      else Nothing
{-
ppDicts dicts = vcat (map msg dicts)
  where
    msg (d:>:p) = sep [ppi p,nest 2 ("from"<+>srcLoc d)]
-}
