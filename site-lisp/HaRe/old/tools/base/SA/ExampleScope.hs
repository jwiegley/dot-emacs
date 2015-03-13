-- $Id: ExampleScope.hs,v 1.2 2001/04/25 17:38:00 moran Exp $

module ExampleScope where

import Syntax
import List(find, nub, nubBy, (\\), sortBy, groupBy, union)
import Maybe
import SyntaxUtil(getTyName)            
import Scope(Senv(..),patBound,allNames,allTypNames
            ,instPatToParts,typePatToParts,boundInP
            ,fst3,fst4,env0,freeT,freeC,restrictTvar)
import Scope2


-------------------------------------------------------------------------
-- free variable example

join (x,y) (a,b) = (x++a,y++b)

extFree :: Bind -> ([HsName],[HsName]) -> ([HsName],[HsName])
extFree (Bpat loc pat) (ev,tv) = (boundInP pat ev,tv)
extFree (Bpats loc ps) (ev,tv) = (foldr boundInP ev ps,tv)
extFree (Bname loc nm) (ev,tv) = (nm:ev,tv)
extFree (Bdecls ds) (ev,tv) = 
    let v = allNames ds env0
    in (map fst (varNames v) ++ map fst3 (constrNames v) ++ ev
       ,map fst4 (classNames v) ++ (tvarNames v) ++ map fst4 (tconstrNames v) ++ tv)
extFree (Btypat tag tp) (ev,tv) = 
    let (tvs, cs)     = allTypNames tp ([], [])             
    in (ev,cs ++ tvs ++ tv)
extFree (Btypats tag tps) (ev,tv) = 
    let (tvs,cs) = allTypNames (hsTyTuple tps) ([],[])
    in (ev,cs ++ tvs ++ tv)
extFree (Btyvar nm) (ev,tv) = (ev,nm : tv)

freelib = Sc extFree id

-----------------------------------------------------------------------
-- When computing free variables type-patterns usually act like binding
-- occurences, so their are no free type-vars in a type-pattern. There
-- is one excpetion and that is in the declarations which make up the
-- where clause of a class definition, then the type patterns inside a
-- type-signature play a different role. The type variables in these
-- type-signatures are not binding, but are in the scope of the type
-- variables introduced by the type-pattern declaring the class.
--
-- class T x where                 <- x is bound here
--    f :: Int -> y -> x           <- vars here are free, so y is free
--    g x = x + h 1 
--        where h :: x -> x        <- these x's are binding
--              h z = z
--
-- This is tricky to handle correctly, since default declarations, may
-- have internal type-signatures which don't obey these special rules
-- but obey the normal rules for type patterns. So we'll parameterize
-- freeD by a boolean that tells if we're immediately inside a Class
-- and make a special mapD function to propogate that information

mapD2 ef pf df tf cf tpf decl =
  case decl of
    HsClassDecl s c tp ds -> HsClassDecl s (cf c) (tpf tp) (df True ds)
    y -> mapD ef pf (df False) tf cf tpf y
    

---------------------------------------------------------- 
freeE :: HsExp -> ([HsName],[HsName]) -> ([HsName],[HsName])

freeE (Exp x) (env @ (ev,tv)) = 
  case x of 
    HsId(HsVar s) -> if elem s ev then ([],[]) else ([s],[])
    x -> accE join join join join join 
           (scopeE freelib env (mapE freeE freeP (freeD False) freeT2 freeC2 x)) 
           ([],[])

freeP :: HsPat -> (HsPat,([HsName],[HsName]) -> ([HsName],[HsName]))
freeP p = (p,const ([],[]))

freeD :: Bool -> [HsDecl] -> ([HsDecl],([HsName],[HsName])->([HsName],[HsName]))  
freeD inClass ds = (ds,free)
  where free env = let v0 = extFree (Bdecls ds) env
                   in (foldr (eachd v0) ([],[]) ds)
        needSpecialRule (HsTypeSig loc nms c t) = inClass
        needSpecialRule other = False
        eachd env (Dec d) ans = 
           if needSpecialRule d
              then let (HsTypeSig loc nms c t) = d
                   in (freeC2 c env) `join` (freeT2 t env) `join` ans
              else accD join join join join join join
                      (scopeD freelib env 
                           (mapD2 freeE freeP freeD freeT2 freeC2 freeTP d))
                      ans    
 
instance Show (a -> b) where
   show g = "<fun>"
                        
freeTP :: HsType -> (HsType,([HsName],[HsName]) -> ([HsName],[HsName]))
freeTP tp = (tp,free)
  where free (ev,tv) = ([],[])
 
freeT2 :: HsType -> ([HsName],[HsName]) -> ([HsName],[HsName])
freeT2 t (ev,tv) = ([],freeT t tv)

freeC2 :: [HsType] -> ([HsName],[HsName]) -> ([HsName],[HsName])
freeC2 cs (ev,tv) = ([],freeC cs tv)
 
testD ds = let (_,f) = freeD False ds in f (extFree (Bdecls ds) ([],[]))

 
-------------------------------------------------------------------------
-- Example extend function for the static env Senv of the static checker


extTvar nm env = env {tvarNames = (nm) : tvarNames env}  
 
extend :: Bind -> Senv -> Senv
extend (Bpat loc pat) env = foldr extName env uniqueNames
        where (uniqueNames,dups,constrArities) = patBound pat ([],[],[])
              extName nm env = env {varNames = (nm,loc) : varNames env}
extend (Bpats loc ps) env = foldr extend env (map (Bpat loc) ps)
extend (Bdecls ds) env = allNames ds env
extend (Bname loc nm) env = env {varNames = (nm,loc) : varNames env}
extend (Btypat tag tp) env = 
  case tag of
        ClassTag ->  -- (Env e x)         -- expects (C v1 ... vn)
          let (constr, tvs) = typePatToParts tp
          in foldr extTvar env tvs 
        InstTag  ->  -- (Env [Int] Bool)  -- expects (C t1 ... tn)
          let (classname, ts) = instPatToParts tp
              (tvs, cs) = foldr allTypNames ([], []) ts
          in foldr extTvar env tvs 
        SigTag   ->  -- (e : typ) 
          let (tvs, cs)     = allTypNames tp ([], [])             
          in foldr extTvar env tvs
extend (Btypats tag (tps @ (constr : args))) env = 
   case tag of
     DataTPS -> foldr (\ t e -> extTvar (getTyName t) e) env tps
     TypeTPS -> foldr (\ t e -> extTvar (getTyName t) e) env args
    
staticlib = Sc extend restrictTvar    

getd = freeD