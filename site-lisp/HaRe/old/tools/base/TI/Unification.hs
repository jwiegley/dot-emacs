{-# OPTIONS -fglasgow-exts #-}
{-# LANGUAGE MultiParamTypeClasses, OverlappingInstances, UndecidableInstances, FunctionalDependencies, NoMonomorphismRestriction #-}
{-+
Generic unification and matching
-}
module Unification where
import Data.Maybe(fromMaybe)
import Data.List(nub)
import MUtils(mapFst,mapSnd,mapBoth,apBoth)

{-+
Term types to be unified (or matched) must be instances of the
following class:
-}
class (Show term,Eq var) => Unifiable term var | term -> var where
  topMatch :: Equation term -> Maybe (Equations term)
  isVar :: term -> Maybe var
  subst :: Substitution var term -> term -> term

  showTerm :: term -> String -- for error reporting with fail

  showTerm = show

type Equation t = (t,t)
type Equations t = [Equation t]

type Substitution v t = [(v,t)]

--mapSubst = mapSnd
mapSubst f s = [seq y (v,y)|(v,x)<-s,let y=f x]-- more strict to avoid space leaks
mapEqns = mapBoth

unify :: (Monad m,Unifiable t v) => Equations t -> m (Substitution v t)
unify = uni []
  where
    -- Invariant: the vars of eqns are not in the domain of s
    --            s is idempotent
    uni s [] = return s
    uni s (eqn@(t1,t2):eqns) =
	case topMatch eqn of
	  Just eqns' -> uni s (eqns'++eqns)
	  _ -> case apBoth isVar eqn of
		(Just v,_) -> varBind v t2
		(_,Just v) -> varBind v t1
		_ -> mismatch' "(unify)" t1 t2
      where
	-- Pre: t is not the variable v. (This is ensured by topMatch.)
	varBind v t =
	  if occurs v t
	  then mismatch' "(occurs check)" t1 t2
          else let s1=(v,t)
		   su=subst [s1]
	       in uni (s1:mapSubst su s) (mapEqns su eqns)


match :: (Monad m,Unifiable t v) => Equations t -> m (Substitution v t)
-- Pre: lhs vars are disjoint from rhs vars
match eqns = uni [] eqns
  where
    pvars = nub $ concatMap (vars.snd) eqns

    -- Invariant: the vars of the lhss of the eqns are not in the domain of s
    uni s [] = return s
    uni s (eqn@(t1,t2):eqns) =
	case topMatch eqn of
	  Just eqns' -> uni s (eqns'++eqns)
	  _ -> case isVar t1 of
		Just v -> varBind v t2
		_ -> mismatch' "(match)" t1 t2
      where
	-- Pre: t is not the variable v. (This is ensured by topMatch.)
	varBind v t =
	  if v `elem` pvars
	  then mismatch' "(matchvar)"  t1 t2
          else let s1=(v,t)
		   su=subst [s1]
	       in uni (s1:mapSubst su s) (mapFst su eqns)

mismatch t1 t2 = mismatch' "" t1 t2
mismatch' s t1 t2 =
  fail ("Mismatch: "++s++"\n  "++showTerm t1++"\nvs\n  "++showTerm t2)

subterms t = map fst $ fromMaybe bug (topMatch (t,t)) -- clumpsy...
  where
    bug = error $
          "Unification: bug in topMatch: term doesn't match itself:"++showTerm t

vars t =
  case isVar t of
    Just v -> [v]
    _ -> nub $ concatMap vars $ subterms t

occurs v t = v `elem` vars t
