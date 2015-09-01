module Scope2(TPtag(..),
              TPStag(..),
              Bind(..),
              Scope(..),
              prop,
              scopeD,
              scopeE,
              scopeT)
where

import Syntax
import List(find, nub, nubBy, (\\), sortBy, groupBy, union)
import Maybe
import SyntaxUtil(isTyVar, getTyName)

------------------------------------------------------------------
-- This module is supposed to capture the details of scoping in Haskell
-- The idea is you supply a bunch of functions with type:
--    pat -> env -> a
-- Since the [Decls] in Haskell are mutually recursive
-- one has to decide who should
-- to the environment which is passed to checkDs result function.
-- e.g. in scopeE for HsLet we say:
--    HsLet (ds,f) e -> 
--       let env2 = ext (Bdecls ds) env 
--       in  HsLet (f env2) (e env2)
-- note how we compute the new env, and pass it to both the ds and the f



data Scope v = Sc (Bind -> v -> v) (v -> v)

data TPtag 
 = ClassTag-- (Env e x)         -- expects (C v1 ... vn)
 | InstTag -- (Env [Int] Bool)  -- expects (C t1 ... tn)
 | SigTag  -- (e : typ)         -- Any type allowed 
 
data TPStag
 = TypeTPS  -- type tp = t
 | DataTPS  -- data tp = C ts | ... | Cn ts  --OR-- newtype tp = C t

data Bind 
 = Bpat SrcLoc HsPat
 | Bpats SrcLoc [ HsPat ]
 | Bdecls [ HsDecl ]
 | Bname SrcLoc HsName
 | Btypat TPtag HsType
 | Btypats TPStag [ HsType ]
 | Btyvar HsName

-----------------------------------------------
-- Whenever we have a list of binding things, like HsPat or typePat
-- we end up with a list of pairs. The first thing in the pair is a
-- binding thing, and the second is the result-producer. What we really
-- want is to build a list of things, and one big result-producer that
-- produces a list of results.

extPairs :: [(b,v->r)] -> ([b],v->[r])    

extPairs [] = ([],const [])
extPairs ((p,g):xs) = (p:ps,h)
   where (ps,g2) = extPairs xs
         h env = (g env) : (g2 env)

prop env f = f env

----------------------------------------    
scopeE :: 
   (Scope v) -> v -> 
   E (v -> e) (HsPat,v -> p) ([HsDecl],v -> ds) (v -> t) (v -> c) -> 
   E e p ds t c

scopeE (lib @ (Sc ext restrict)) env x =
  case x of
    HsLet (ds,f) e -> 
       let env2 = ext (Bdecls ds) env 
       in  HsLet (f env2) (e env2)
    HsLambda pairs e -> 
       let (ps,psf) = extPairs pairs 
           env2 = ext (Bpats loc0 ps) env
       in HsLambda (psf env) (e env2)
    HsCase e alts -> HsCase (e env) (map (scopeAlt lib env) alts)
    HsDo stmt -> HsDo (scopeStmt lib env stmt)
    HsListComp stmt -> HsListComp (scopeStmt lib env stmt)
    other -> mapE (prop env) (prop env . snd) (prop env . snd) (prop env) (prop env) other
                           
----------------------------------------
scopeStmt :: 
  (Scope v) -> v -> 
  HsStmt (v -> e) (HsPat,v -> p) ([HsDecl],v -> ds) ->
  HsStmt e p ds
  
scopeStmt (lib @ (Sc ext restrict)) env x =
  case x of 
   (HsGenerator (p,pf) e s) ->
      let env2 = ext (Bpat loc0 p) env 
      in HsGenerator (pf env) (e env2) (scopeStmt lib env2 s)
   (HsQualifier e s) -> HsQualifier (e env) (scopeStmt lib env s)
   (HsLetStmt (ds,dsf) s) ->
      let env2 = ext (Bdecls ds) env 
      in HsLetStmt (dsf env2) (scopeStmt lib env2 s)
   (HsLast e) -> HsLast (e env)   

----------------------------------------
scopeAlt :: 
   (Scope v) -> v -> 
   HsAlt (v -> e) (HsPat,v -> p) ([HsDecl],v -> ds) ->
   HsAlt e p ds

scopeAlt (Sc ext restrict) env (HsAlt s (p,pf) rhs (ds,dsf)) = 
    let env2 = ext (Bpat s p) env
        env3 = ext (Bdecls ds) env2
    in  (HsAlt s (pf env) (scopeRhs env3 rhs) (dsf env3))

-----------------------------------------
scopeRhs :: v -> HsRhs (v -> e) -> HsRhs e
scopeRhs env x = mapRhs (prop env) x


--------------------------------------------
scopeD :: 
    (Scope v) -> v -> 
    D (v -> e) (HsPat, v -> p) ([HsDecl], v -> ds) (v -> t) (v -> c) (HsType, v -> tp) -> 
    D e p ds t c tp 

scopeD (lib @ (Sc ext restrict)) env x =
  let scopConDecl env = mapConDecl (prop env) 
      extendWithTvs env tvs = foldr (\ nm v -> ext (Btyvar nm) v) env tvs
      scopMatch env (HsMatch loc nm pairs rhs (ds,df)) = 
        let (ps,psf) = extPairs pairs 
            env2 = ext (Bpats loc ps) env
            env3 = ext (Bdecls ds) (ext (Bname loc nm) env2)
        in HsMatch loc nm (psf env) (scopeRhs env3 rhs) (df env3)
  in
  case x of
    HsPatBind loc (p,pf) rhs (ds,dsf) ->
        let env1 = ext (Bpat loc p) env
            env2 = ext (Bdecls ds)  env1
        in HsPatBind loc (pf env) (scopeRhs env2 rhs) (dsf env2)
    HsFunBind loc matches -> HsFunBind loc (map (scopMatch env) matches)
    HsTypeDecl loc pairs tf -> 
        let (ts,tsf) = extPairs pairs 
            env2 = ext (Btypats TypeTPS ts) env
        in HsTypeDecl loc (tsf env) (tf env2)   
    HsNewTypeDecl loc contxtf pairs condecl derivs ->
        let (ts,tsf) = extPairs pairs 
            env2 = ext (Btypats DataTPS ts) env
            env3 = ext (Btypats TypeTPS ts ) (restrict env)
        in  HsNewTypeDecl loc (contxtf env3) (tsf env) (scopConDecl env2 condecl) derivs      
    HsDataDecl loc contxtf pairs condecls derivs ->
        let (ts,tsf) = extPairs pairs 
            env2 = ext (Btypats DataTPS ts) env
            env3 = ext (Btypats TypeTPS ts ) (restrict env)
        in  HsDataDecl loc (contxtf env3) (tsf env) (map (scopConDecl env2) condecls) derivs 
    HsClassDecl loc contxtf (tp,tpf) (ds,dsf) ->    
         let env1 = ext (Btypat ClassTag tp) (restrict env)
             env2 = ext (Btypat ClassTag tp) env
         in HsClassDecl loc (contxtf env1) (tpf env1) (dsf env2) 
    HsInstDecl loc contxtf (tp,tpf) (ds,dsf) ->    
         let env1 = ext (Btypat InstTag tp) (restrict env)
             env2 = ext (Btypat InstTag tp) env
         in HsInstDecl loc (contxtf env1) (tpf env1) (dsf env2) 
    HsTypeSig loc nms contxtf (tp, tpf)  ->
         let env1 = ext (Btypat SigTag tp) env
         in HsTypeSig loc nms (contxtf env1) (tpf env)
    z -> mapD (prop env) h h (prop env) (prop env) h z
         where h (x,f) = error "Binding case in scopeD not handled"      

--------------------------------------------------------------------------
-- Then for the type sub-language

scopeT :: v -> T (v -> t) -> T t
scopeT env t = mapT (\f -> f env) t       
 
