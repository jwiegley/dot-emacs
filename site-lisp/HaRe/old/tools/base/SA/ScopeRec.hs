-- $Id: ScopeRec.hs,v 1.1 2001/07/24 17:39:10 moran Exp $

module ScopeRec where 

import Syntax
import List(find, nub, nubBy, (\\), sortBy, groupBy, union)
--import Observe
import PrettyPrint
import Maybe
import IOExts
import SyntaxUtil(isTyVar, getTyName)
import Scope2
import HsConstants
import ScopeStruct

names :: HsDecl -> Senv
names (Dec d) = namesD d

dataName (HsConDecl s nm slots) = (nm, s, length slots)
dataName (HsRecDecl s nm slots) = (nm, s, length slots)

recordName :: HsConDecl t -> [(HsName, SrcLoc)] 
recordName (HsConDecl s nm slots) = []
recordName (HsRecDecl s nm slots) = foldr f [] slots
    where f (names,domain) xs = map (\nm -> (nm,s)) names ++ xs
  
allNames :: [HsDecl] -> Senv -> Senv  
allNames ds initial = foldr acc initial ds
  where acc d env = concatEnv (names d) env 


----------------------------------------------------------------------         
-- Generic Static checking functions

duplicates :: Eq a => [a] -> [a]
duplicates [] = []
duplicates (x:xs) = 
  if elem x xs then x : (duplicates (filter (/=x) xs)) else (duplicates xs)

collect_duplicate_info :: ([a] -> [b]) -> (a -> a -> Ordering) -> [a] -> [b]
collect_duplicate_info infof compare = 
  concat . (map infof) . (groupBy (lift compare)) . (sortBy compare)
    where lift g x y = case g x y of { EQ -> True; _ -> False }

dupErrs :: (Show a, Show b) => b -> [(a,SrcLoc)] -> [Error]
dupErrs sort [] = []
dupErrs sort [x] =[]
dupErrs sort xs@((nm,loc):_) = chk loc True (duplicate_things sort nm (map snd xs))

dupTvErr srcloc [x]    = []
dupTvErr srcloc (x:xs) = [(srcloc, duplicate_type_vars x)]

chk:: SrcLoc -> Bool -> String -> [Error]
chk loc test message = if test then [(loc,message)] else []

unique :: Eq a => [(a,b)] -> [(a,b)]
unique = nubBy (\(a,_) (b,_) -> a==b)


------------------------------------------------------------------------------
-- Scope checking 
------------------------------------------------------------------------------
nmConflict :: Senv -> [Error]
nmConflict env = 
    let ts = tconstrNames env 
        cs = classNames env
        sameName (tn,tloc,_,_) errs =
          case find (\(a,_,_,_) -> a==tn) cs of 
            Nothing           -> errs
            Just (_,cloc,_,_) -> (tloc, type_class_conflict tn [tloc,cloc]) : errs
    in  foldr sameName [] ts

classMethodErr :: Senv -> [Error]
classMethodErr env = 
   let ss = sigNames env
       vs = varNames env
       sigExists (vn,vloc) errs =
         case find (\(a,_) -> a==vn) ss of
           Nothing      -> (vloc, method_without_signature vn) : errs
           Just _       -> errs
   in  foldr sigExists [] vs

type_class_conflict tn cloc = 
  "Type name " ++ pp tn ++ " is used as class name "++ pp cloc 
method_without_signature vn = 
  "Definition of " ++ pp vn  ++ " without declaration"



getClass (Typ (HsTyApp x _)) = getClass x
getClass (Typ (HsTyCon c))   = Just c
getClass _                   = Nothing


allTypNames (Typ (HsTyVar v)) (vs, cs) = (v : vs, cs)
allTypNames (Typ (HsTyCon c)) (vs, cs) = (vs,     c : cs)
allTypNames (Typ t)           ans      = accT allTypNames t ans

isTyConApp (Typ (HsTyCon _))   = True
isTyConApp (Typ (HsTyApp f _)) = isTyConApp f
isTyConApp _                   = False

getTyAppArgs (Typ (HsTyCon _))   args = args
getTyAppArgs (Typ (HsTyApp f x)) args = getTyAppArgs f (x:args)

-- Well formed type expression: C x*
wfTp :: SrcLoc -> TPContext -> HsType -> [Error] -> [Error]
wfTp srcloc c t errs =
    if isTyConApp t && all isTyVar (getTyAppArgs t []) then
        errs
    else
        (srcloc, type_former_is_not_constructor t c) : errs

-- well formed simple class specification: C x+
wfSclass :: SrcLoc -> HsType -> [Error] -> [Error]
wfSclass loc t errs =
    if isTyConApp t && not (null args) && all isTyVar args then
        errs
    else
        (loc, illformed_sclass t) : errs
    where args = getTyAppArgs t []

 

-------------------------------------------------------------------------

srcloc (HsTypeDecl          loc  _ _     ) = loc
srcloc (HsNewTypeDecl       loc  _ _ _ _ ) = loc
srcloc (HsDataDecl          loc  _ _ _ _ ) = loc
srcloc (HsClassDecl         loc  _ _ _   ) = loc
srcloc (HsInstDecl          loc  _ _ _   ) = loc
srcloc (HsDefaultDecl       loc  _       ) = loc
srcloc (HsTypeSig           loc  _ _ _   ) = loc
srcloc (HsFunBind           loc  _       ) = loc
srcloc (HsPatBind           loc  _ _ _   ) = loc
srcloc (HsPrimitiveTypeDecl loc  _ _     ) = loc
srcloc (HsPrimitiveBind     loc  _ _     ) = loc

whatIs (HsTypeDecl          _  _ _     ) = "type declaration"
whatIs (HsNewTypeDecl       _  _ _ _ _ ) = "newtype declaration"
whatIs (HsDataDecl          _  _ _ _ _ ) = "data declaration"
whatIs (HsClassDecl         _  _ _ _   ) = "class declaration"
whatIs (HsInstDecl          _  _ _ _   ) = "instance declaration"
whatIs (HsDefaultDecl       _  _       ) = "declaration"
whatIs (HsTypeSig           _  _ _ _   ) = "type signature"
whatIs (HsFunBind           _  _       ) = "function binding"
whatIs (HsPatBind           _  _ _ _   ) = "pattern binding"
whatIs (HsPrimitiveTypeDecl _  _ _     ) = "declaration"
whatIs (HsPrimitiveBind     _  _ _     ) = "declaration"


--------------------------------------------------------------
-- The first kind of scoping and its combinators
--------------------------------------------------------------

scopE :: v -> E (v -> e) (v->v,v -> p) (v->v,v -> ds) (v -> t) (v -> c) -> E e p ds t c
scopE env x =
  case x of
    HsLet (envtrans,f) e -> let env2 = envtrans env 
                            in  HsLet (f env2) (e env2)
    HsLambda ps e        -> let (env2,ps') = scopPatList env ps  
                            in  HsLambda ps' (e env2)
    HsCase e alts        -> HsCase (e env) (map (scopAlt env) alts)
    HsDo stmt            -> HsDo (scopStmt env stmt)
    HsListComp stmt      -> HsListComp (scopStmt env stmt)
    
    z -> mapE (\ f -> f env) (error "missing HsExp case") 
              (error "missing HsDecl case") (\ f -> f env) (\ f -> f env) z

scopAlt :: v -> HsAlt (v -> e) (v->v,v -> p) (v->v,v -> ds) -> HsAlt e p ds
scopAlt env (HsAlt s (f,pf) rhs (g,dsf)) = 
    let env2 = g (f env)
    in  (HsAlt s (pf env) (scopRhs env2 rhs) (dsf env2))

scopRhs :: v -> HsRhs (v -> e) -> HsRhs e
scopRhs env x = mapRhs (\ f -> f env) x

scopStmt :: v -> HsStmt (v -> e) (v->v,v -> p) (v->v,v -> ds) -> HsStmt e p ds
scopStmt env (HsGenerator (tr,pf) e s) = 
   let env2 = tr env in HsGenerator (pf env) (e env2) (scopStmt env2 s)
scopStmt env (HsQualifier e s) = HsQualifier (e env) (scopStmt env s)
scopStmt env (HsLetStmt (tf,dsf) s) = 
   let env2 = tf env in HsLetStmt (dsf env2) (scopStmt env2 s)
scopStmt env (HsLast e) = HsLast (e env)   

scopPatList :: v -> [(v -> v,v -> p)] -> (v,[p])
scopPatList env ps = (foldr (\ (tf,_ ) e -> tf e) env ps,
                      map (\ (_ ,pf)   -> pf env) ps)

--------------------------------------------------------------------------
-- Then for the declaration sub-language

scopD :: Env v => v -> 
         D (v -> e)
         (v -> v, v -> p)
         (v -> v, v -> ds)
         (v -> t)
         (v -> c)
         (v -> v, v -> tp) -> 
         D e p ds t c tp 
scopD env x =
  let scopConDecl env = mapConDecl (\f -> f env) 
      extendWithTvs env tvs = foldr extTvar env tvs
      scopMatch env (HsMatch loc nm ps rhs (dectrans,ds)) = 
        let (env2,ps') = scopPatList env ps
            env3 = dectrans (extVar nm loc env2)
        in HsMatch loc nm ps' (scopRhs env3 rhs) (ds env3)
  in
  case x of
    HsPatBind loc (pattrans,pf) rhs (dectrans,dsf) ->
        let env2 = dectrans (pattrans env)
        in
        HsPatBind loc (pf env) (scopRhs env2 rhs) (dsf env2)
    HsFunBind loc matches -> HsFunBind loc (map (scopMatch env) matches)
    HsTypeDecl loc (transtpfs @ ((ctrans,cmaker):fs)) tf -> 
        let env2 = ctrans env
            constr = cmaker env
            (env3,args) = scopPatList env fs
        in HsTypeDecl loc (constr:args) (tf env3)
        
    HsNewTypeDecl loc contxtf transtpfs condecl derivs ->
          let (env2,args) = scopPatList env transtpfs
              (env3,_) = scopPatList (restrictTvar env) (tail transtpfs)
          in  HsNewTypeDecl loc (contxtf env3) args  (scopConDecl env2 condecl) derivs
    
    HsDataDecl loc contxtf transtpfs condecls derivs ->
         let (env2,args) = scopPatList env transtpfs
             (env3,_) = scopPatList (restrictTvar env) (tail transtpfs)
         in  HsDataDecl loc (contxtf env3) args (map (scopConDecl env2) condecls) derivs
    
    HsClassDecl loc contxtf (trans,tpf) (dectrans,dsf) ->    
         let env1 = trans (restrictTvar env) 
         in HsClassDecl loc (contxtf env1) (tpf env) (dsf $ dectrans env1) 
    HsInstDecl loc contxtf (trans,tpf) (dectrans,dsf) ->    
         let env1 = trans (restrictTvar env) 
         in HsInstDecl loc (contxtf env1) (tpf env) (dsf $ dectrans env1) 
    HsTypeSig loc nms contxtf (transf, tpf)  ->
         HsTypeSig loc nms (contxtf (transf env)) (tpf env)
    z -> mapD (\ f -> f env) h h (\ f -> f env) (\ f -> f env) (error "type pattern") z
         where h (trans,f) = f (trans env) 


--------------------------------------------------------------------------
-- Then for the type sub-language

scopT :: v -> T (v -> t) -> T t
scopT env t = mapT (\f -> f env) t 

--------------------------------------------------------------------------
-- Computing Things about patterns
--------------------------------------------------------------------------

boundInP :: HsPat -> [HsName] -> [HsName]
boundInP (Pat(HsPId(HsVar s))) ans = s:ans
boundInP (Pat(HsPAsPat n p)) ans = boundInP p (n:ans)
boundInP (Pat x) ans = accP boundInP ans x


------------------------------------------------------------------------
    -- patBound: Compute three things while visiting each pattern sub-node.
    -- 1) A list of unique names bound by the pattern
    -- 2) A list of names that appear more than once. 
    --    These are errors because we allow only linear patterns
    -- 3) A list of every construtor and the arity at which it was used.
    --    These are potential errors if the arites do not match

patBound :: HsPat -> ([HsName], [HsName], [(HsName, Int)]) -> 
                     ([HsName], [HsName], [(HsName, Int)])
patBound (Pat p) ans =
    case p of
    HsPId(HsVar n)      -> add n ans
    HsPAsPat n p        -> patBound p (add n ans) 
    HsPApp c ps         -> cadd c (length ps) ans'
    HsPInfixApp p1 c p2 -> cadd (getHSName c) 2 ans'
    _                   -> ans'

    where add x (a, b, c) = 
               if elem x a 
                  then if elem x b 
                          then (a, b, c)
                          else (a, x:b, c)  
                  else (x:a, b, c)
          cadd c n (x, y, z) = (x, y, (c, n):z)
          ans' = accP patBound ans p


------------------------------------------------------------------------------
-- Static Check for Expressions

chE :: SrcLoc -> HsExp -> Senv -> [Error]
chE loc (exp @ (Exp x)) env =
  case scopE env (mapE (chE loc) (chP loc)
               (chDs WhereLikeDecl) (chT loc ) (error "ctxt")  x) of
    HsId (HsVar n) -> chk loc (not (varDefined n env)) (undefined_variable n)
    HsInfixApp x (HsVar n) y -> chk loc (not (varDefined n env)) (undefined_variable n)
    HsLeftSection x (HsVar n) -> chk loc (not (varDefined n env)) (undefined_variable n)
    HsRightSection (HsVar n) x -> chk loc (not (varDefined n env)) (undefined_variable n)
    HsLambda ps e -> e ++ (chPatList loc env ps)
  
    z -> accE (++) (\ (ns,errs) a -> errs++a) (++) (++) (++) z []
    
--------------------------------------------
-- Static checks for individual patterns

chP :: SrcLoc -> HsPat -> (Senv -> Senv,Senv -> ([HsName],[Error]))
chP loc (pat @ (Pat x)) = (envTrans, f)
  where (uniqueNames,dups,constrArities) = patBound pat ([],[],[])
        envTrans env = foldr extName env uniqueNames
        extName nm = extVar nm loc
        duperr = chk loc (not (null dups)) (duplicate_vars_in_pattern dups)
        f env = (uniqueNames,allErrors env)
        allErrors env = foldr arityCheck duperr constrArities
          where arityCheck (c,n) ans = check c n (cArity c env) ++ ans
                check c n Nothing  = [(loc,undefined_constr c)]
                check c n (Just m) = chk loc (m /=n) (constr_wrong_arity n c)

-----------------------------------------------------------------------------
-- When language constructs have a list of patterns like : (\ p1 ... pn -> e)
-- or (case x of { C p1 ... pn -> e }), Haskell has the rule that no variable
-- should appear more than once in the list. We can't check this, pattern by
-- pattern, but have to observe the complete list. If we map (chP env) over a
-- list of patterns we get [([unique_names],[error_messages])], from this we
-- can compute additional error_messages dealing with duplicates.

chPatList :: SrcLoc -> Senv -> [([HsName],[Error])] -> [Error]      
chPatList loc env ps =
 let accumulate (ns,errs) (names,errors) = (ns++names,errs++errors)
     (allbound,internalerr) = foldr accumulate ([],[]) ps
     dups = duplicates allbound
     duperr = chk loc (not (null dups)) (repeated_pattern_variables dups)
 in internalerr ++ duperr

--------------------------------------------------------------------------
-- static checks for a list of Decls


chDs :: DeclContext -> [HsDecl] -> (Senv->Senv,Senv -> [Error] )
chDs contxt ds = (envtrans,errorfun)
  where env      = allNames ds env0
        envtrans = concatEnv env
        errorfun env = foldr (\ d ans -> (check env d) ++ ans) allErrors ds
        sameName (x,y) (a,b) = compare x a
        contextErrors = catMaybes $ map (legal contxt) ds
        dupErr k message = collect_duplicate_info (dupErrs message) sameName (locations k env)
        dupValErrors  = dupErr Var    "value definitions"
        dupSigErrors  = dupErr Sig    "type signatures"
        dupClsErrors  = dupErr Class  "class definitions"
        dupTypErrors  = dupErr TyCons "type definitions"
        dupConsErrors = dupErr Cons   "constructor functions"

        allErrors = contextErrors++dupValErrors++dupSigErrors++dupClsErrors
                    ++ dupTypErrors ++ dupConsErrors ++ nmConflict env ++ clsMethodErr
        sigerr loc name = chk loc ((not $ elem name (map fst (varNames env))) && contxt/=ClassDecl)
                                  (signature_without_definition name)
        methodErr c (nm,loc) = chk loc (not $ isMethod nm c env) (not_a_method nm c)
        clsMethodErr = case contxt of 
                       ClassDecl -> classMethodErr env
                       other     -> []
        check env (Dec x) =
          let loc = srcloc x
              methodErrs (HsInstDecl loc c tp ds) = 
                let nms = varNames $ allNames ds env0
                in  case getClass tp of
                     Nothing -> []
                     Just c  -> concat $ map (methodErr c) nms
          in
           case scopD env (mapD' (chE loc) (chP loc) (chDs) (chT loc) (chCntxt loc) (chTp loc) x) of
             HsTypeSig loc nms c t  -> (concat $ map (sigerr loc) nms)++c++t
             HsInstDecl loc c tp ds -> methodErrs x ++ c ++ tp ++ ds
             z -> accD (++) (\ (ns,errs) a -> (errs)++a) (++) (++) (++) (++) z []

    
    
---------------------------------------------------------------------------

chT :: SrcLoc -> HsType -> Senv -> [Error]
chT loc (typ @ (Typ t)) env = 
  case t of 
   HsTyVar nm -> chk loc (not (tvarDefined nm env)) (undefined_tvar nm)
   HsTyCon nm -> chk loc (not (tconDefined nm env)) (undefined_tcon nm)
   HsTyApp (Typ f) x -> synCheck (chT loc) env f x 1
   z -> accT (++) (scopT env (mapT (chT loc)  z)) []

synCheck chf env (HsTyCon c) arg n = 
    case synArity c env of
    Nothing -> chk loc (not (tconDefined c env)) (undefined_tcon c) ++ chf arg env 
    Just m  -> chk loc (m/=n) (tysynonym_not_fully_applied c) ++ chf arg env
synCheck chf env (HsTyApp (Typ f) x) arg n =
    synCheck chf env f x (n+1) ++ chf arg env
synCheck chf env t arg n = chf (Typ t) env ++ chf arg env

-----------------------------------------------------------------------------
-- Static checks for contexts

chCntxt :: SrcLoc ->  DeclContext -> [HsType] -> (Senv -> [Error])
chCntxt loc c ts env = foldr (check c) [] ts
  where inscope (Typ (HsTyVar x)) ans = 
            chk loc (not $ tvarDefined x env) (undefined_tvar_in_context x) ++ ans
        inscope (Typ (HsTyCon c)) ans = 
            chk loc (not $ classDefined c env) (undefined_class_in_context c) ++ ans 
        inscope (Typ x) ans  = accT inscope x ans 

        -- class: C (x t*)+
        wfClass t (Typ (HsTyApp (Typ (HsTyCon c)) x )) xs =
           wfClassArg x x xs
        wfClass t (Typ (HsTyApp x y ))                 xs =
           wfClass t x $ wfClassArg x x xs
        wfClass t (Typ x)                              xs =
           (loc, illformed_class t) : xs

        -- class arg: x t*
        wfClassArg t (Typ (HsTyVar y))   xs = xs
        wfClassArg t (Typ (HsTyApp x _)) xs = wfClassArg t x xs 
        wfClassArg t (Typ x)             xs = (loc, illformed_class_arg t) : xs

        check ClassDecl x ans = wfSclass loc x (inscope x ans)
        check InstDecl  x ans = wfSclass loc x (inscope x ans)
        check _         x ans = wfClass  x x   (inscope x ans)

-----------------------------------------------------------------------------
-- Static checks for type patterns


chTp :: SrcLoc ->  TPContext -> HsType -> (Senv -> Senv, Senv -> [Error])
chTp srcloc InstTP x =
  let errors = wf x []
      -- well formed instance: C (C x*)+

      wf (Typ(HsTyApp (Typ(HsTyCon c)) arg)) xs =
         wfTp srcloc InstTP arg xs
      wf (Typ(HsTyCon c)) xs                 =
         (srcloc, instance_required c) : xs 
      wf (Typ(HsTyApp y arg)) xs             =
         wf y (wfTp srcloc InstTP arg xs)
      wf tp xs                               =
         (srcloc, instance_not_class_app tp) : xs

      (classname, ts) = instPatToParts x
      (tvs, cs) = foldr allTypNames ([], []) ts
      trans env = if null errors then foldr extTvar env tvs else env
      clsError env = chk srcloc (not $ classDefined classname env) 
                                (undefined_class_in_instance classname)
      cdef env c ans = 
         if tconDefined c env 
         then case synArity c env of
              Nothing   -> ans
              Just _    -> (srcloc, synonym_illegal_in_instance c):ans
         else (srcloc,undefined_tcon_in_instance c):ans
      dupErrs = collect_duplicate_info (dupTvErr srcloc) compare tvs
      tpf env = if null errors
                then foldr (cdef env) (dupErrs ++ clsError env) cs
                else errors
  in (trans, tpf)                

chTp srcloc SigTP x =
  let (tvs, cs)     = allTypNames x ([], [])
      trans env    = foldr extTvar env tvs
      cdef env c ans = 
         if tconDefined c env 
         then ans
         else (srcloc, undefined_tcon_in_signature c):ans
      tpf env = foldr (cdef env) [] cs
  in  (trans, tpf)

chTp srcloc cntxt x =
  let (constr, tvs) = typePatToParts x
      errors = case cntxt of DataLikeTP ->  wfTp     srcloc cntxt x []
                             ClassTP    ->  wfSclass srcloc       x []
      trans env = if null errors then foldr extTvar env tvs else env
      tpf env   = if null errors 
                  then collect_duplicate_info (dupTvErr srcloc) compare tvs
                  else errors
  in (trans, tpf)



-------------------------------------------------------------------------
-- Error Message Strings are computed here
-------------------------------------------------------------------------

undefined_variable nm = "Undefined variable: "++ pp nm
duplicate_vars_in_pattern dups =
  "Variables appear more than once in single pattern: " ++ pp dups
undefined_constr c =
  "Undefined Constructor in pattern: " ++ pp c
constr_wrong_arity n c =
  "Constructor "++ pp c++ " must have exactly "++ pp n ++ " arguments."
repeated_pattern_variables dups =
  "Repeated variables in pattern list: " ++ pp dups
duplicate_things sort name locs =
  "Duplicate " ++ show sort ++ " of " ++ show name ++
  " at locations: " ++ pp locs
signature_without_definition name =
  "Signature for "++pp name++" without matching definition."

undefined_class_in_instance classname =
  "Class name in instance: " ++ pp classname ++ "  is not defined"
undefined_tcon_in_instance c =
  "Type constructor " ++ pp c ++ " in instance is not defined"
synonym_illegal_in_instance c =
  "Type synonym " ++ pp c ++ " in instance"

undefined_tcon_in_signature c =
  "Type constructor " ++ pp c ++ " in signature is not defined"
  
undefined_class_in_context clsname =
  "Class name " ++ pp clsname ++ " in context is not defined"
undefined_tvar_in_context tvarname =
  "Type variable " ++ pp tvarname ++ " in context is not defined"
undefined_tvar tvarname =
  "Type variable " ++ pp tvarname ++ "  is not defined"
undefined_tcon tconname =
  "Type constructor " ++ pp tconname ++ "  is not defined"
tysynonym_not_fully_applied tyconname =
  "Type synonym " ++ pp tyconname ++ "  is not fully applied"
duplicate_type_vars x =
  "Duplicate type variables in definition: " ++ pp x

non_tyvar_arg_in_pattern a c =
  "Argument in Type Pattern in " ++ show c ++ " is not a variable: "++ pp a
type_former_is_not_constructor x c = 
  "Type pattern in " ++ show c ++ " is not an application of a type constructor: "++ pp x
instance_required tp =
  "Instance of class " ++ pp tp ++ " required"
instance_not_class_app tp = 
  "Instance is not an application of a class constructor: "++pp tp

illformed_sclass t=
  "ill formed class "++pp t
illformed_class t=
  "ill formed class in context "++pp t
illformed_class_arg t=
  "ill formed argument " ++ pp t ++ " to class in context "

not_a_method nm c =
  pp nm ++ " is not a method of class " ++ pp c

{-

showAst === pp

showAst :: Printable a => a -> String
showAst = render . ppi
-}

----------------------------------------------------------------------------------
-- some tests

sh :: Printable b => b -> IO ()
sh = putStr . render . ppi

loc = SrcLoc "Scope tests" 0 0

names2 @ [fn,gn,hn,kn,xn,yn,zn] = map UnQual ["f","g","h","k","x","y","z"]
names3 @ [an,bn,cn,dn,en,tn,sn] = map UnQual ["A","B","C","D","E","T","S"]

exps @  [fe,ge,he,ke,xe,ye,ze] = map hsEVar  names2
pats @  [fp,gp,hp,kp,xp,yp,zp] = map hsPVar  names2
typs @  [ft,gt,ht,kt,xt,yt,zt] = map hsTyVar names2

cons @  [ac,bc,cc,dc,ec,tc,sc] = map hsECon  names3
tcons @ [at,bt,ct,dt,et,tt,st] = map hsTyCon names3

ap2 [x] = x
ap2 (x:y:xs) = ap2((hsApp x y):xs)

apt [x] = x
apt (x:y:xs) = apt((hsTyApp x y):xs)

arr = hsTyFun


class1 = hsClassDecl loc [] (apt [ct,xt])
           [ hsTypeSig loc [fn] [] (xt `arr` xt) ]
class2 = hsClassDecl loc [apt[ct,yt]] (apt [dt,yt])
           [ hsTypeSig loc [gn] [] (yt `arr` yt) ]
class3 = hsClassDecl loc [apt[at,yt,xt]] (apt [et,yt,yt])
           [ hsTypeSig loc [zn] [] (yt `arr` yt) ]         

inst0 = hsInstDecl loc [] (ct) []
inst0'= hsInstDecl loc [] (xt) []
inst1 = hsInstDecl loc [] (apt [ct,xt]) []
inst2 = hsInstDecl loc [] (apt [ct,apt [dt,xt,xt]]) []
inst3 = hsInstDecl loc [] (apt [ct,apt [dt,at]]) []
inst4 = hsInstDecl loc [apt [dt,xt]] (apt [ct,tt]) []
inst5 = hsInstDecl loc [] (apt [ct,at]) []
inst6 = hsInstDecl loc [] (yt `arr` yt) []

data1 = hsDataDecl loc [] [tt] [HsConDecl loc cn []] []
data2 = hsDataDecl loc [] [tt,xt] [] []
data3 = hsDataDecl loc [] [tt] [HsConDecl loc cn [HsBangedType yt]
                             ,HsConDecl loc dn [HsUnBangedType at]
                             ,HsConDecl loc dn []
                             ] []
data4 = hsDataDecl loc [] [tt,xt] [HsConDecl loc dn [HsUnBangedType st]] []
data5 = hsDataDecl loc [] [tt,xt] [HsConDecl loc dn [HsUnBangedType (apt [st,xt])]] []
data6 = hsDataDecl loc [] [tt,xt] [HsConDecl loc dn [HsUnBangedType (apt [st,xt,yt])]] []
data7 = hsDataDecl loc [] [tt,xt] [HsConDecl loc dn [HsUnBangedType (apt [st,xt,yt,yt])]] []

type1 = hsTypeDecl loc [st,xt,yt] (hsTyTuple [xt,yt])
sig1  = hsTypeSig loc [zn] [] (apt [st,xt])

p0 = [class1,class2,class3,inst1,inst2,inst3]
p1 = [inst2]
p2 = [class1,class1,data1,data2,inst4,inst5]

run env prog  = let (f,x) = chDs TopDecl prog in x(f env)
ss  = run env0 

showErr (SrcLoc f n m, s) = "(" ++ show n ++ ", " ++ show m ++ ") " ++ s

sck ds = (putStr . unlines . map showErr . ss) ds
        
test prog = do {sh prog; putStr "\n------------\n"; sck prog}

testDs :: (String,[HsDecl]) -> IO ()
testDs (s, ds) = 
         do { putStr "\n==============================================\n"
            ; putStr s
            ; putStr "\n--- test code----------\n"
            ; sh ds
            ; putStr "\n--- errors ------------\n"
            ; (putStr . unlines . map showErr . run env0) ds
            }

tests ts = sequence_ $ map testDs ts

insts :: [(String, [HsDecl])]
insts = [ ("Ill formed instance type", [ hsInstDecl loc [] (ct) [] ] )
        , ("Ill formed instance type", [ hsInstDecl loc [] (xt) [] ])
        , ("Ill formed instance type", [hsInstDecl loc [] (apt [ct,xt]) []])
        , ("Undefined class & type" , [hsInstDecl loc [] (apt [ct,dt]) []])
        , ("Duplicate type vars", 
                [ hsDataDecl  loc [] [dt] [] []
                , hsClassDecl loc [] (apt [ct,xt]) []
                , hsInstDecl loc [] (apt [ct,apt [dt,xt,xt]]) []])
        , ("Argument to TyCon must be tyvar", [hsInstDecl loc [] (apt [ct,apt [dt,at]]) []])
        , ("Many undefined", [hsInstDecl loc [apt [dt,xt]] (apt [ct,tt]) []])
        , ("Type synonym illegal",   
                 [ hsTypeDecl  loc [at] bt
                 , hsDataDecl  loc [] [bt] [] []
                 , hsClassDecl loc [] (apt [ct,xt]) []
                 , hsInstDecl  loc [] (apt [ct,at]) []
                 ])
        , ("Context errors", 
                [ hsDataDecl  loc [] [at] [] []
                , hsDataDecl  loc [] [bt,xt] [] []
                , hsClassDecl loc [] (apt [ct,xt]) []
                , hsClassDecl loc [] (apt [dt,xt]) []
                , hsInstDecl  loc [xt] (apt [ct,at]) []
                , hsInstDecl  loc [dt] (apt [ct,at]) []
                , hsInstDecl  loc [apt[dt,apt[xt,yt]]] (apt [ct,apt [bt,xt]]) []
                ])
        , ("",
                [ hsDataDecl  loc [] [at] [] []
                , hsClassDecl loc [] (apt [ct,xt]) [ hsTypeSig loc [fn] [] (xt `arr` xt) ]
                , hsInstDecl  loc [] (apt [ct,at]) 
                        [ hsTypeSig loc [fn] [] (xt `arr` xt) 
                        , hsFunBind loc [HsMatch loc fn [xp] (HsBody(hsEVar xn)) []] 
                        , hsFunBind loc [HsMatch loc gn [xp] (HsBody(hsEVar yn)) []] 
                        ]
                ])
        , ("OK", [ hsDataDecl  loc [] [at] [] []
                 , hsDataDecl  loc [] [bt,xt] [] []
                 , hsClassDecl loc [] (apt [ct,xt]) []
                 , hsClassDecl loc [] (apt [dt,xt]) []
                 , hsInstDecl  loc [] (apt [ct,at]) []
                 , hsInstDecl  loc [apt [dt,xt]] (apt [ct,apt [bt,xt]]) []
                 ])
        , ("class/type name conflict", 
                 [ hsDataDecl  loc [] [at] [] []
                 , hsDataDecl  loc [] [bt] [] []
                 , hsInstDecl loc [] (apt [at,bt]) []
                 , hsInstDecl loc [] (apt [ct,bt]) []
                 ] )
                           
        ]

dts  = [ ("", [ hsDataDecl  loc [] [at,bt] [] [] ] )
       , ("", [ hsDataDecl  loc [] [xt,yt] [] [] ] )
       ]

clss = [ ("OK", [hsClassDecl loc [] (apt [ct,xt]) []])
       , ("ill formed class specification", [hsClassDecl loc [] (ct) []])
       , ("ill formed class specification", [hsClassDecl loc [] (xt) []])
       , ("class/type name conflict", 
                [ hsDataDecl  loc [] [at] [] []
                , hsDataDecl  loc [] [bt] [] []
                , hsClassDecl loc [] (apt [at,xt]) []
                , hsClassDecl loc [] (apt [bt,xt]) []
                ] )
       , ("ill formed class specification", 
                [  hsClassDecl loc [] (apt [ct,at]) []
                ] )
       , ("ill formed class specification", 
                [  hsClassDecl loc [] (apt [ct,at]) []
                ,  hsClassDecl loc [] (apt [dt,at]) []
                ] )
       , ("ill formed class specification", 
                [ hsDataDecl  loc [] [at] [] []
                , hsClassDecl loc [] (apt [ct,at]) []
                ] )
       , ("",
                [  hsClassDecl loc [] (apt [ct,xt])
                   [ hsTypeSig loc [fn] [] (arr xt xt)
                   , hsPatBind loc fp (HsBody (hsLambda [xp] xe)) []
                   , hsPatBind loc gp (HsBody (hsLambda [xp] xe)) []
                   ]
                ] )
       ]
      
patBind p e = hsPatBind loc p (HsBody e) []

d1 = [patBind fp (hsLambda [xp] xe), patBind fp (hsLambda [xp] (xe))]
{-
p2 = [hsTypeSig loc [zn] (TypeUnQual$ hsTyCon (UnQual "Int"))]
p3 = [hsTypeSig loc [yn,yn] (TypeUnQual $ Typ $ HsTyCon (UnQual "Int"))]
p4 = [patBind fp (hsLet [patBind xp ye] xe)]
p5 = [patBind fp (hsLambda [xp] (ye))]
p6 = [patBind fp (hsLambda [hsPTuple [xp, xp], xp] ye)]
p7 = [patBind fp (hsLambda [hsPTuple [xp, xp, xp], xp] ye)]

runP p = let (envt,f) = chP loc p in f (envt env0)
-}

-----------------------------------------------------------------------------
-- computing free variables
-- Computing free variables is a tricky computation, because the same variable
-- may be free in one spot and bound in another. We need an environment to
-- determine what variables are bound at any particular point. We use a list
-- of HsName as the environment

-- Given an expression and an environment telling what vars are bound
-- determine the free variables in the expression.

freeE :: HsExp -> [HsName] -> [HsName]
freeE (Exp x) env = 
  case scopE env (mapE freeE freeP freeD freeT freeC x) of
    HsId(HsVar s) -> if elem s env then [] else [s]
    HsInfixApp x (HsVar s) y -> if elem s env then [] else [s]
    HsLeftSection x (HsVar s) -> if elem s env then [] else [s]
    HsRightSection (HsVar s) x -> if elem s env then [] else [s]
    x -> accE (++) (++) (++) (++) (++) x []
            

-- Return a pair of functions. The first is an env transformer, adding
-- the vars in the pattern, the second is a function given an env, which
-- determines the free vars in the pattern. The second is the constant []
-- function since patterns only introduce variables, they only have binding
-- occurences.

freeP :: HsPat -> ([HsName]->[HsName],[HsName]->[HsName])
freeP p = ((vs++),const [])
  where vs = boundInP p []
        
-- Return a pair of functions. The first is an env transformer, adding
-- the vars declared by the list of Decls, the second is a function which
-- when given an env, determines the free vars in the Decls 

freeD :: [HsDecl] -> ([HsName]->[HsName],[HsName]->[HsName])
freeD ds = (ext,free)
  where bound = foldr add [] ds
        ext env = bound ++ env 
        add (Dec (HsPatBind s p rhs ds)) env = boundInP p env
        add (Dec (HsFunBind s ((HsMatch s2 nm ps rhs ds):_))) env  = nm : env
        add (Dec (HsDataDecl s ctx typats condecls derivings)) env =
           getTyName (head typats) : env
        add (Dec (HsTypeDecl s typats t)) env = getTyName (head typats) : env
        add d env = env
        getNameOfTypat (Typ x) = 
             case x of 
               HsTyApp l _ -> getNameOfTypat l
               HsTyCon n   -> n
               HsTyVar n   -> n 
               _           -> error "getNameOfTypat "
        free env = (foldr (f env) [] ds) \\ bound 
        f env (Dec d) ans = 
          accD (++)(++)(++)(++)(++)(++)
               (scopD env (mapD (\ x -> ( (freeE x))) freeP freeD freeT freeC freeTP d)) ans
ff env (Dec d) ans = 
          accD (++)(++)(++)(++)(++)(++)
               (scopD env (mapD (\ x -> ( (freeE x))) freeP freeD freeT freeC freeTP d)) ans          


instance Env [HsName] where
  extClass n l a args env = env
  extTconstr n l a b  env = n:env
  extTvar n           env = n:env
  extConstr n l a     env = n:env
  extVar n l          env = n:env
  extSig n l          env = env
  extMod n            env = env
  env0 = []
  restrictTvar env = env


-- Given an environment holding bound variables, return the 
-- free variables in the HsType

freeT :: HsType -> [HsName] -> [HsName]
freeT (Typ x) env = 
  case scopT env (mapT freeT x) of
    HsTyCon n -> if elem n env then [] else [n]    
    HsTyVar n -> if elem n env then [] else [n]
    x         -> accT (union) x []

allFree :: HsType -> [HsName] -> [HsName]
allFree (Typ x) ans = 
  case x of
    HsTyCon n -> union [n] ans
    HsTyVar n -> union [n] ans
    x         -> accT allFree x ans


-- compute the free variables in a context.

freeC :: [HsType] -> [HsName] -> [HsName]
freeC x env = concat (map (\z -> freeT z env) x)

-- Type patterns are HsTYpes which act as binding occurences. Hence
-- they return a pair. First an env transformer, and Second a function
-- that given an env, computes the TypePatterns free variables. Like patterns
-- this always returns []

freeTP :: HsType -> ([HsName] -> [HsName],[HsName] -> [HsName])
freeTP x = (allFree x,const [])


makeSCC ds env =
  let (envtrans,_) = freeD ds 
      bound = envtrans []
      oneD d = let (_,free) = freeD [d] in free env
      oneBind d = let (envt,_) = freeD [d] in envt []
      allFree  = map oneD ds
      allBound = map oneBind ds 
  in (allFree,allBound)

--------------------------------------------------------------------------
-- Contexts
--------------------------------------------------------------------------

-- type patterns appear in 4 different contexts

data TPContext = DataLikeTP | ClassTP | InstTP | SigTP
instance Show TPContext where
  show DataLikeTP = "type, data, or newtype declaration"
  show ClassTP    = "class declaration"
  show InstTP     = "instance declaration"
  show SigTP      = "type signature" 


-----------------------------------------------------------------
-- Lists of declarations can appear in four different contexts
-- Only certain kinds of declarations are legal in some of these.

data DeclContext = TopDecl | ClassDecl | InstDecl | WhereLikeDecl deriving (Eq)
instance Show DeclContext where
  show TopDecl       = "top level"
  show ClassDecl     = "class declaration"
  show InstDecl      = "class declaration"
  show WhereLikeDecl = "local declaration"

legal :: DeclContext -> HsDecl -> Maybe Error
legal context (d @ (Dec x)) =
  let err context x = Just (srcloc x,
                "Illegal "++ whatIs x ++" in " ++ show context)
  in  case (context,x) of
      (TopDecl,   any)                             -> Nothing
      (ClassDecl, HsTypeSig _ _ _ _)               -> Nothing
      (ClassDecl, HsFunBind _ _)                   -> Nothing
      (ClassDecl, HsPatBind _ (Pat(HsPId(HsVar _))) _ _) -> Nothing
      (ClassDecl, any)                             -> err context x
      (InstDecl,  HsFunBind _ _)                   -> Nothing
      (InstDecl,  HsPatBind _ (Pat(HsPId(HsVar _))) _ _) -> Nothing
      (InstDecl,  any)                             -> err context x
      (WhereLikeDecl, HsTypeSig _ _ _ _)           -> Nothing
      (WhereLikeDecl, HsFunBind _ _)               -> Nothing
      (WhereLikeDecl, HsPatBind _ _ _ _)           -> Nothing
      (WhereLikeDecl, any)                         -> err context x

-----------------------------------------------------------------------
-- MapD' is like mapD, except it know what kind of contexts are
-- appropriate and passes this information downwards

mapD' :: (a -> b) -> (c -> d) -> (DeclContext -> e -> f) -> (g -> h) -> (DeclContext -> i -> j)
                  -> (TPContext -> k -> l) -> D a c e g i k -> D b d f h j l
mapD' ef pf df tf cf tpf decl =
   case decl of
    HsTypeDecl s tps t -> 
        HsTypeDecl s (map (tpf DataLikeTP) tps) (tf t)
    HsNewTypeDecl s cntxt tps cd names ->
        HsNewTypeDecl s (cf TopDecl cntxt)
              (map (tpf DataLikeTP) tps) (mapConDecl tf cd) names
    HsDataDecl s cntxt tps cds names   ->
        HsDataDecl s (cf TopDecl cntxt)
               (map (tpf DataLikeTP) tps)
               (map (mapConDecl tf) cds) names
    HsClassDecl s c tp ds                   ->
        HsClassDecl s (cf ClassDecl c) (tpf ClassTP tp) (df ClassDecl ds)
    HsInstDecl s c tp ds                    ->
        HsInstDecl s (cf InstDecl c) (tpf InstTP tp) (df InstDecl ds)
    HsDefaultDecl s t -> 
        HsDefaultDecl s (tf t)
    HsTypeSig s nms c t                  ->
        HsTypeSig s nms (cf TopDecl c) (tpf SigTP t)
    HsFunBind s matches                   ->
        HsFunBind s (map (mapMatch ef pf (df WhereLikeDecl)) matches)
    HsPatBind s p rhs ds                  ->
        HsPatBind s (pf p) (mapRhs ef rhs) (df WhereLikeDecl ds)
    HsPrimitiveTypeDecl s cntxt nm        -> 
        HsPrimitiveTypeDecl s (cf TopDecl cntxt) nm
    HsPrimitiveBind s nm t                ->
        HsPrimitiveBind s nm (tf t) -- Hugs compatibility


 
-------------------------------------------------------------------
-------------------------------------------------------------------
-- Static Checking using Bind based scoping

-------------------------------------------------------------------------
-- Example extend function for the static env Senv of the static checker


-- extTvar nm env = env {tvarNames = (nm) : tvarNames env}  
 
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

------------------------------------------------------------------
-- Static checks for expressions 

checkE :: SrcLoc -> HsExp -> Senv -> [Error]
checkE loc (exp @ (Exp x)) env =
  case scopeE staticlib env 
         (mapE (checkE loc) (checkP loc)
               (checkDs WhereLikeDecl) (checkT loc) (checkCnxt loc WhereLikeDecl)  x) of
    HsId (HsVar n) -> chk loc (not (varDefined n env)) (undefined_variable n)
    HsInfixApp x (HsVar n) y -> chk loc (not (varDefined n env)) (undefined_variable n)
    HsLeftSection x (HsVar n) -> chk loc (not (varDefined n env)) (undefined_variable n)
    HsRightSection (HsVar n) x -> chk loc (not (varDefined n env)) (undefined_variable n)
    HsLambda ps e -> e ++ (checkPList loc env ps)
    z -> accE (++) (\ (nm,err) a -> err ++ a) (++) (++) (++) z []
    
-----------------------------------------------------------------------------
-- When language constructs have a list of patterns like : (\ p1 ... pn -> e)
-- or (case x of { C p1 ... pn -> e }), Haskell has the rule that no variable
-- should appear more than once in the list. We can't check this, pattern by
-- pattern, but have to observe the complete list. If we map (chP env) over a
-- list of patterns we get [([unique_names],[error_messages])], from this we
-- can compute additional error_messages dealing with duplicates.

checkPList :: SrcLoc -> Senv -> [([HsName],[Error])] -> [Error]      
checkPList loc env ps =
 let accumulate (ns,errs) (names,errors) = (ns++names,errs++errors)
     (allbound,internalerr) = foldr accumulate ([],[]) ps
     dups = duplicates allbound
     duperr = chk loc (not (null dups)) (repeated_pattern_variables dups)
 in internalerr ++ duperr

--------------------------------------------
-- Static checks for individual patterns

checkP ::  SrcLoc -> HsPat -> (HsPat, Senv -> ([HsName],[Error]))
checkP loc (pat @ (Pat x)) = (pat, f)
  where (uniqueNames,dups,constrArities) = patBound pat ([],[],[])
        duperr = chk loc (not (null dups)) (duplicate_vars_in_pattern dups)
        f env = (uniqueNames,allErrors env)
        allErrors env = foldr arityCheck duperr constrArities
          where arityCheck (c,n) ans = check c n (cArity c env) ++ ans
                check c n Nothing  = [(loc,undefined_constr c)]
                check c n (Just m) = chk loc (m /=n) (constr_wrong_arity n c)


------------------------------------------------------------------------------
-- Static Check for Expressions

-- checkDs assumes that all the names in the [Decl] have already been added
-- to the environment which is passed to checkDs result function.
-- e.g. in scopeE for HsLet we say:
--    HsLet (ds,f) e -> 
--       let env2 = ext (Bdecls ds) env 
--       in  HsLet (f env2) (e env2)
-- note how we compute the new env, and pass it to both the ds and the f

checkDs ::  DeclContext -> [HsDecl] -> ([HsDecl],Senv -> [Error])
checkDs contxt ds = (ds,errorfun)
  where env      = allNames ds env0
        errorfun env = foldr (\ d ans -> (check env d) ++ ans) allErrors ds
        sameName (x,y) (a,b) = compare x a
        contextErrors = catMaybes $ map (legal contxt) ds
        dupErr k message = collect_duplicate_info (dupErrs message) sameName (locations k env)
        dupValErrors  = dupErr Var    "value definitions"
        dupSigErrors  = dupErr Sig    "type signatures"
        dupClsErrors  = dupErr Class  "class definitions"
        dupTypErrors  = dupErr TyCons "type definitions"
        dupConsErrors = dupErr Cons   "constructor functions"

        allErrors = contextErrors++dupValErrors++dupSigErrors++dupClsErrors
                    ++ dupTypErrors ++ dupConsErrors ++ nmConflict env ++ clsMethodErr
        sigerr loc name = chk loc ((not $ elem name (map fst (varNames env))) && contxt/=ClassDecl)
                                  (signature_without_definition name)
        methodErr c (nm,loc) = chk loc (not $ isMethod nm c env) (not_a_method nm c)
        clsMethodErr = case contxt of 
                       ClassDecl -> classMethodErr env
                       other     -> []
        check env (Dec x) =
          let loc = srcloc x
              methodErrs (HsInstDecl loc c tp ds) = 
                let nms = varNames $ allNames ds env0
                in  case getClass tp of
                     Nothing -> []
                     Just c  -> concat $ map (methodErr c) nms
          in
           case scopeD staticlib env 
                  (mapD' (checkE loc) (checkP loc) (checkDs) 
                         (checkT loc) (checkCnxt loc) (checkTp loc) x) of
             HsTypeSig loc nms c t  -> (concat $ map (sigerr loc) nms)++c++t
             HsInstDecl loc c tp ds -> methodErrs x ++ c ++ tp ++ ds
             z -> accD (++) (\ (ns,errs) a -> (errs)++a) (++) (++) (++) (++) z []

---------------------------------------------------------------------------
-- static checks for types

checkT ::  SrcLoc -> HsType -> Senv -> [Error]
checkT loc (typ @ (Typ t)) env = 
  case t of 
   HsTyVar nm -> chk loc (not (tvarDefined nm env)) (undefined_tvar nm)
   HsTyCon nm -> chk loc (not (tconDefined nm env)) (undefined_tcon nm)
   HsTyApp (y @ (Typ f)) x -> synArityCheck (checkT loc) env f x 1
   z -> accT (++) (scopeT env (mapT (checkT loc)  z)) []

synArityCheck chf env typ arg n = 
  case typ of
    (HsTyCon c) -> 
       case synArity c env of
         Nothing -> chk loc (not (tconDefined c env)) (undefined_tcon c) ++ chf arg env 
         Just m  -> chk loc (m/=n) (tysynonym_not_fully_applied c) ++ chf arg env
    (HsTyApp (Typ f) x) -> synArityCheck chf env f x (n+1) ++ chf arg env
    t -> chf (Typ t) env ++ chf arg env
   
----------------------------------------------------------------------
-- Static Checking for contexts

checkCnxt :: SrcLoc -> DeclContext -> [HsType] -> Senv -> [Error]

checkCnxt loc c ts env = foldr (check c) [] ts
  where inscope (Typ (HsTyVar x)) ans = 
            chk loc (not $ tvarDefined x env) (undefined_tvar_in_context x) ++ ans
        inscope (Typ (HsTyCon c)) ans = 
            chk loc (not $ classDefined c env) (undefined_class_in_context c) ++ ans 
        inscope (Typ x) ans  = accT inscope x ans 

        -- class: C (x t*)+
        wfClass t (Typ (HsTyApp (Typ (HsTyCon c)) x )) xs =
           wfClassArg x x xs
        wfClass t (Typ (HsTyApp x y ))                 xs =
           wfClass t x $ wfClassArg x x xs
        wfClass t (Typ x)                              xs =
           (loc, illformed_class t) : xs

        -- class arg: x t*
        wfClassArg t (Typ (HsTyVar y))   xs = xs
        wfClassArg t (Typ (HsTyApp x _)) xs = wfClassArg t x xs 
        wfClassArg t (Typ x)             xs = (loc, illformed_class_arg t) : xs

        check ClassDecl x ans = wfSclass loc x (inscope x ans)
        check InstDecl  x ans = wfSclass loc x (inscope x ans)
        check _         x ans = wfClass  x x   (inscope x ans)


---------------------------------------------------------------------
-- Static checks for type-patterns

--checkTp ::  SrcLoc -> TPContext -> HsType -> (HsType,Senv -> [Error])
checkTp :: SrcLoc ->  TPContext -> HsType -> (HsType, Senv -> [Error])

checkTp srcloc InstTP x =
  let errors = wf x []
      -- well formed instance: C (C x*)+

      wf (Typ(HsTyApp (Typ(HsTyCon c)) arg)) xs =
         wfTp srcloc InstTP arg xs
      wf (Typ(HsTyCon c)) xs                 =
         (srcloc, instance_required c) : xs 
      wf (Typ(HsTyApp y arg)) xs             =
         wf y (wfTp srcloc InstTP arg xs)
      wf tp xs                               =
         (srcloc, instance_not_class_app tp) : xs

      (classname, ts) = instPatToParts x
      (tvs, cs) = foldr allTypNames ([], []) ts
      clsError env = chk srcloc (not $ classDefined classname env) 
                                (undefined_class_in_instance classname)
      cdef env c ans = 
         if tconDefined c env 
         then case synArity c env of
              Nothing   -> ans
              Just _    -> (srcloc, synonym_illegal_in_instance c):ans
         else (srcloc,undefined_tcon_in_instance c):ans
      dupErrs = collect_duplicate_info (dupTvErr srcloc) compare tvs
      tpf env = if null errors
                then foldr (cdef env) (dupErrs ++ clsError env) cs
                else errors
  in (x, tpf)                

checkTp srcloc SigTP x =
  let (_, cs)     = allTypNames x ([], [])
      cdef env c ans = 
         if tconDefined c env 
         then ans
         else (srcloc, undefined_tcon_in_signature c):ans
      tpf env = foldr (cdef env) [] cs
  in  (x, tpf)

checkTp srcloc cntxt x =
  let (_, tvs) = typePatToParts x
      errors = case cntxt of DataLikeTP ->  wfTp     srcloc cntxt x []
                             ClassTP    ->  wfSclass srcloc       x []
      tpf env   = if null errors 
                  then collect_duplicate_info (dupTvErr srcloc) compare tvs
                  else errors
  in (x, tpf)

-----------------------------------------------------------------
-- Running the basic tests

run2 env prog  = let (ds,f) = checkDs TopDecl prog in (f (allNames ds env))

new (_,x) = run2 env0 x
old (_,x) = run env0 x

test2 :: (String,[HsDecl]) -> IO ()
test2 (s, ds) = 
         do { putStr "\n==============================================\n"
            ; putStr s
            ; putStr "\n--- test code----------\n"
            ; sh ds
            ; putStr "\n--- errors ------------\n"
            ; (putStr . unlines . map showErr . run2 env0) ds
            }

tests2 ts = sequence_ (map test2 ts)

errors1 ts = map (run2 env0) (map snd ts) 
errors2 ts = map (run env0) (map snd ts)        
             
new1 = errors1 insts       
old1 = errors2 insts

oks = zipWith (==) old1 new1


[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11] = insts

gg x = concat(map (\ (y,_,_,_) -> show y) (classNames x))
------------------------------------------------------------------
-- extra stuff



-- supply a unique integer string
count :: IORef Int
count = unsafePerformIO $ newIORef 0
initCount = writeIORef count 10
incCount a = unsafePerformIO $ do { c <- readIORef count
                                  ; writeIORef count $! (c+1)
                                  ; return c
                                  }

uniqueStr a = show $ incCount ()
