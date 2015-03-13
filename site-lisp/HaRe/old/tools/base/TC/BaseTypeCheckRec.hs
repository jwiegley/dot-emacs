-- $Id: BaseTypeCheckRec.hs,v 1.2 2001/09/29 00:08:23 diatchki Exp $

module BaseTypeCheckRec where

import BaseSyntaxStruct
import TypeGenerics
import List(nub)

--------------------------------------------------------------------


type Type a   = U a Kind T
type NGV a    = [(HsName, U a Kind T)]
type Env a    = [(HsName, Scheme Kind (U a Kind T))]
type Genfun a = String -> Im a Error HsName
type Alt      = HsAlt HsDecl HsExp HsPat
type Stmt     = HsStmt HsDecl HsExp HsPat


type EnvNew a = [Assump HsName Kind (U a Kind T)]

data GEnv a = GEnv [(HsName,Class a)] (NGV a) [Assump HsName Kind (U a Kind T)]

data Class a = Class HsName [Class a] [Inst a] 
type Inst a  = ([Pred (U a Kind T)], (Pred (U a Kind T)))

name  (GEnv cs ngv ass) x = let Class nm sup inst = look cs x in nm
super (GEnv cs ngv ass) x = let Class nm sup inst = look cs x in sup
insts (GEnv cs ngv ass) x = let Class nm sup inst = look cs x in ass 


------------------------------------------------------------------------
-- Instance declaration to make the T functor from HsSyn.hs appropriate
-- for doing type checking ala Hmx.hs

instance G T where
  seqG = seqT
  mapG = mapT
  accG = accT
  
instance Name T HsName where
  isName (HsTyVar s) = Just s
  isName _ = Nothing
  fromName s = HsTyVar s
  
instance Gensym a HsName where
  newGensym  =
    do { seed <- newRef (1::Int)
       ; let gensym s = do { n <- readVar seed
                           ; writeVar seed (n+1)
                           ; return (UnQual (s ++ (show n)))
                           }
         in return gensym
       } 
       
  gensym s = do { n <- nextN   
                ; return (UnQual (s ++ (show n)))
                }

data Error 
    = MatchError String (Vis T) (Vis T)
    | KErr String (Vis K) (Vis K)   
   
instance TypeError Error T Kind where 
  hmxError s x y = 
    do { (nms,[x',y']) <- visible (generic []) [x,y]
       ; raise (MatchError s x' y')
       }

-----------------------------------------------------------

type NGVars a = [(HsName,U a Kind T)]

emptyNGVars :: NGVars a
emptyNGVars = []

extendNGVars :: HsName -> U a Kind T -> NGVars a -> NGVars a
extendNGVars s t ngvars = (s,t):ngvars

generic :: NGVars a -> U a Kind T -> Im a e Bool 
generic ngvars v = do { b <- occursInList v ngvars; return (not b) }
     where occursInList v l =
            do { (TVar v') <- prune v
               ; bools <- mapM (\ (a,b) -> occursIn v' b) l
               ; return (or bools)
               }
       
--------- Show Instances ----------------------------------
                             
instance Show(U a k T) where 
  showsPrec n (S x) = shows x
  showsPrec n (TGen m) = showString "%" . shows m
  showsPrec n (TVar _) = showString "?"

instance Show(Vis T) where 
  showsPrec n (VN a) = showString a
  showsPrec n (VS x) = shows x  
  

instance Show a => Show(Pred a) where
  show (IsIn n ts) = "(" ++ n ++ " " ++ (show ts) ++ ")"

instance Show a => Show (Scheme Kind a) where
  show (Sch x p t) = "(all " ++ (show x) ++"." ++ (show p) ++ " => " ++ (show t) ++ ")"  


----------------------- Instantiate unification ------------------------------

unifyShape unify ( x @ (S tx)) (y @ (S ty)) =
  case (tx,ty) of
   (HsTyFun x1 x2,HsTyFun y1 y2) ->
      do { xs <- unify x1 y1 
         ; ys <- unify x2 y2 
         ; return (xs++ys) }     
   (HsTyTuple xs,HsTyTuple ys) ->
      if (length xs) == (length ys)  
         then do { xss <- mapM (uncurry unify) (zip xs ys)
                 ; return (concat xss)
                 }
         else hmxError "TupleLengthMatch" x y
   (HsTyApp x1 x2,HsTyApp y1 y2) ->
      do { xs <- unify x1 y1 
         ; ys <- unify x2 y2 
         ; return (xs++ys) }   
   (HsTyVar n1,HsTyVar n2) ->
      if n1 == n2 
         then return []
         else hmxError "NameMatch" x y 
   (HsTyCon n1,HsTyCon n2) ->
      if n1 == n2 
         then return []
         else hmxError "NameMatch" x y          
   (tx,ty) -> hmxError "ShapeMatch"  x y
      

unify :: (U a Kind T) -> (U a Kind T) ->  Im a Error [p]
unify = unifier (hmxError "OccursCheck") unifyShape
     
     
------------------ Kind inference -----------------------
data Sort = Sort
type Knd a = U a Sort K

instance G K where
  mapG = mapK
  seqG = seqK
  accG f = flip (accK f)

instance TypeError Error K Sort where
  hmxError s x y = 
    do { (nms,[x',y']) <- visible (\ x -> return False) [x,y]
       ; raise (KErr s x' y')
       }

unifyK unify ( x @ (S tx)) (y @ (S ty)) =
  case (tx,ty) of
   (Kstar,Kstar) -> return []
   (Kfun x1 x2,Kfun y1 y2) ->
      do { xs <- unify x1 y1 
         ; ys <- unify x2 y2 
         ; return (xs++ys) }   
   (tx,ty) -> hmxError "KindShapeMatch"  x y
      
unifyKind :: (U a Sort K) -> (U a Sort K) ->  Im a Error [p]
unifyKind = unifier (hmxError "OccursCheck") unifyK

star = S Kstar 

inferK :: (HsName -> U a Sort K) -> U a Sort K -> HsType -> Im a Error (U a Sort K)
inferK env hint (Typ typ) =
  case typ of
    (HsTyFun x y) ->
       do { x' <- inferK env star x
          ; y' <- inferK env star y
          ; unifyKind hint star
          ; return hint
          }
    (HsTyTuple ts) ->
       do { sequence (map (inferK env star) ts)
          ; unifyKind hint star
          ; return star
          }
    (HsTyApp x y) ->
       do { a <- newVar Sort
          ; b <- newVar Sort
          ; x' <- inferK env (S(Kfun a hint)) x
          ; y' <- inferK env a y
          ; return hint
          }
    (HsTyVar nm) ->
       do { unifyKind hint (env nm)
          ; return hint
          }
    (HsTyCon nm) ->  
       do { unifyKind hint (env nm)
          ; return hint
          }

kindOf :: (HsName -> U a Sort K) -> HsType -> Im a Error Kind
kindOf envf x = do { hint <- newVar Sort
                   ; inferK envf hint x
                   ; k <- uaSortK_to_Kind hint
                   ; return k
                   }
       
----------------------------------------------------------------------------
-- After Kind inference some of the Kind Vars may still be un-instantiated
-- Since we do not have a "polymorphic" Kind system we must instantiate
-- these Kind vars. We fix them to kind "Knd Kstar", and then turn the 
-- resulting (U a Sort K)  thing into a "Kind" type.

uaSortK_to_Kind :: (U a Sort K) -> Im a e Kind
uaSortK_to_Kind (S x) = do { x' <- seqG(mapG uaSortK_to_Kind x); return (Knd x')}
uaSortK_to_Kind (TGen m) = error "no TGen in kinds"
uaSortK_to_Kind (t @ (TVar x)) = follow finish uaSortK_to_Kind t
    where finish :: (Tyvar a Sort K) -> Im a e Kind
          finish (Tyvar ref s) = do { writeVar ref (Just star)
                                    ; return (Knd Kstar) }
                 
     
--------------- Environment function and types --------------------------


extend f s t = (s,t) : f

lambdaExt :: [(name,Scheme a c)] -> name -> c -> [(name,Scheme a c)]
lambdaExt env vname vtyp = extend env vname (Sch [] [] vtyp)

envf [] s = error ("variable not found: "++(show s)++"\n")
envf ((x,t):m) s = if x==s then t else envf m s

-------- Type constructors and types of literal constants ------------

tArrow x y = S(HsTyFun x y)
tTuple ts = S(HsTyTuple ts)
tInteger = S(HsTyCon (UnQual "Integer"))
tChar = S(HsTyCon (UnQual "Char"))
tString = tlist tChar
tRational = S(HsTyCon (UnQual "Rational"))
tBool = S(HsTyCon (UnQual "Bool"))

tStringHash = S(HsTyCon (UnQual "stringHash"))
tCharHash = S(HsTyCon (UnQual "CharHash"))
tIntHash = S(HsTyCon (UnQual "IntHash"))
tRationalHash = S(HsTyCon (UnQual "RationalHash"))
tlist x =  S(HsTyApp tlistCon x)
tlistCon = (S(HsTyCon (UnQual "[]")))

tcode x =  S(HsTyApp tcodeCon x)
tcodeCon = (S(HsTyCon (UnQual "Code")))

litTyp (HsInt _)        = tInteger
litTyp (HsChar _)       = tChar
litTyp (HsString _)     = tString
litTyp (HsFrac _)       = tRational
litTyp (HsCharPrim _)   = tCharHash
litTyp (HsStringPrim _) = tStringHash
litTyp (HsIntPrim _)    = tIntHash
litTyp (HsFloatPrim _)  = tRationalHash
litTyp (HsDoublePrim _) = tRationalHash

------------------------ Predefined Class predicates ----------------

num x = IsIn "Num" [x] 
monad x = IsIn "Monad" [x]
enum x = IsIn "Enum" [x]

-------------------------------------------------------------------------
-- unArrow [p1,p2,p3] (t1 -> t2 -> t3 -> t4) ---> (t4,[(p1,t1),(p2,t2),(p3,t3)])

unArrow :: [HsPat] -> Type a -> Im a Error (Type a,[(HsPat,Type a)])
unArrow ps t = do { t' <- col t; flat ps t' }
  where flat (p:ps) (S(HsTyFun dom rng)) = 
          do { (t,ts) <- (flat ps rng) ; return (t,(p,dom) : ts) }
        flat [] t = return (t,[])
        flat (p:ps) t = error "Too many arguments to pattern"


patExtTup [] env = return ([],[],[])
patExtTup ((p,t):m) env = 
    do { (t1,e1,c1) <- patExt p t env
       ; (ts,e2,cs) <- patExtTup m env 
       ; return(t1:ts,e1++e2,c1 ++ cs)
       }

patExtList []    elemtyp env cs = return (tlist elemtyp,[],cs)
patExtList (p:m) elemtyp env cs = 
    do { (t1,e1,c1) <- patExt p elemtyp env
       ; (listOfelem,e2,cs) <- patExtList m elemtyp env c1
       ; return(listOfelem,e1 ++ e2,c1++cs)
       }


patExt :: HsPat -> Type a -> Env a -> Im a Error (Type a,NGV a,[Pred (Type a)])
patExt (Pat p) typ env =
  case p of
   (HsPVar name) -> return (typ,[(name,typ)],[])
   (HsPLit l) -> 
      do { let t = litTyp l
         ; cs <- unify t typ
         ; return (t,[],cs)
         }
   (HsPNeg x) -> error "whats this?"
   (HsPInfixApp x n y) -> patExt (Pat(HsPApp n [x,y])) typ env 
   (HsPApp nm ps) -> 
      do { (cs1 :=> ctyp) <- instan (envf env nm) 
         ; (t,patTypeList) <- unArrow ps ctyp
         ; cs2 <- unify t typ
         ; (ts2,env2,cs3) <- patExtTup patTypeList env 
         ; return (t,env2,cs1 ++ cs2 ++ cs3)
         }
   (HsPTuple ps) ->
      do { ts <- sequence (map (\ x -> (newVar kstar)) ps)
         ; cs2 <- unify (tTuple ts) typ
         ; (ts,ngv3,cs3) <- patExtTup (zip ps ts) env
         ; return (tTuple ts,ngv3,cs2 ++ cs3)
         }         
   (HsPList ps ) -> 
      do { elemtyp <- newVar kstar
         ; (listtyp,ngv2,cs) <- patExtList ps elemtyp env []
         ; cs2 <- unify listtyp (tlist elemtyp)
         ; return (listtyp,ngv2,cs ++ cs2)
         }        
   (HsPParen x) -> patExt x typ env
   (HsPRec n pairs) -> error "not yet"
   (HsPRecUpdate nm pairs) -> error "not yet"
   (HsPAsPat name x) ->
      do { (t,ngv1,cs1) <- patExt x typ env
         ; return (t,(name,t):ngv1,cs1)
         }
   (HsPWildCard) -> do { t <- newVar kstar ; return (t,[],[]) }
   (HsPIrrPat x) -> patExt x typ env

inferPats :: [HsPat] -> NGV a -> Env a ->  
               Im a Error ([Type a],NGV a,Env a,[Pred (Type a)])
inferPats ps ngvars env =
  do { pairs <- sequence (map (\ p -> do { t <- newVar kstar; return (p,t) }) ps)
     ; (t1,ngv1,cs1) <- patExtTup pairs env
     ; return (t1,ngv1 ++ ngvars,g ngv1 env,cs1)
     }  where g [] env = env
              g ((v,t):more) env = lambdaExt (g more env) v t
  
inferPat p ngvars env hint =
  do { (_,ngv1,cs1) <- patExt p hint env
     ; return (ngv1 ++ ngvars,g ngv1 env,cs1)
     }  where g [] env = env
              g ((v,t):more) env = lambdaExt (g more env) v t
    
-------------------------------------------------------------
    

infer :: Genfun a -> NGV a -> Env a -> Type a ->
            HsExp -> Im a Error (Type a,[Pred (Type a)])            
infer gensym ngvars env hint (exp @ (Exp e)) =
  let check env hint x = infer gensym ngvars env hint x 
  in
  case e of
    HsVar nm -> 
      do { (cs :=> t) <- instan (envf env nm)
         ; cs2 <- unify t hint
         ; return (t,cs ++ cs2)
         }
    HsCon nm -> 
      do { (cs :=> t) <- instan (envf env nm)
         ; cs2 <- unify t hint
         ; return (t,cs++cs2)
         }
    HsLit n -> 
      do { let t = litTyp n
         ; cs <- unify t hint
         ; return (t,cs)
         }         
    HsInfixApp x f y -> check env hint (Exp(HsApp (Exp (HsApp f x)) y))
    HsApp f x ->
      do { xtyp <- newVar kstar
         ; let ftyp = tArrow xtyp hint   
         ; (_,cs2) <- check env xtyp x
         ; (_,cs3) <- check env ftyp f
         ; return (hint,cs2++cs3)
         }
    HsNegApp x ->
      do { (t,cs) <- check env hint x
         ; return (t,num t : cs)
         }
    HsLambda ps x ->
      do { (ptyps,ngv2,env2,cs) <- inferPats ps ngvars env
         ; result <- newVar kstar
           -- f [t1,t2,t3] r --> (t1 -> t2 -> t3 -> r)
         ; let f [] rng = rng
               f (t:ts) rng = tArrow t (f ts rng)
         ; (_,cs2) <- infer gensym ngv2 env2 result x
         ; return (f ptyps result,cs ++ cs2)
         }  
    HsLet ds e -> 
      do { (ngv2,env2,cs2) <- inferDecls gensym ngvars env ds
         ; infer gensym  ngv2 env2 hint e
         }
    HsIf x y z -> 
      do { t <- newVar kstar
         ; (_,cs1) <- check env tBool x
         ; (_,cs2) <- check env t y
         ; (_,cs3) <- check env t z
         ; return (t,cs1 ++ cs2 ++ cs3)
         }    
    HsCase e alts -> 
      do { argtyp <- newVar kstar
         ; (ptyp,cs1) <- check env argtyp e
         ; csAll <- mapM (inferAlt gensym ngvars env ptyp hint) alts
         ; return (hint, cs1 ++ concat csAll)
         }
    HsDo stmt -> 
      do { mtyp <- newVar (karrow kstar kstar)
         ; let m x =  (S(HsTyApp mtyp x))
         ; a <- newVar kstar
         ; cs2 <- unify hint (m a)
         ; cs3 <- inferStmt gensym ngvars env mtyp (m a) False stmt
         ; return (hint,(monad mtyp) : cs2 ++ cs3)
         }
    HsTuple xs -> 
      do { pairs <- sequence (map (\ x -> do { t <- newVar kstar; return (t,x) }) xs)
         ; let tupletyp = tTuple(map fst pairs)
         ; cs1 <- unify hint tupletyp
         ; ts <- mapM (uncurry (check env)) pairs
         ; return (hint,foldr (\ (t,c) cs -> c ++ cs) cs1 ts)
         }
    HsList xs -> 
      do { elemtyp <- newVar kstar
         ; cs1 <- unify hint (tlist elemtyp)
         ; pairs <- mapM (check env elemtyp) xs
         ; return (hint,foldr (\ (t,c) cs -> c ++ cs) cs1 pairs)
         }
    HsParen x -> check env hint x
    HsRightSection oper arg ->  -- i.e.  (+ 3) }
      do { ltyp <- newVar kstar
         ; rtyp <- newVar kstar
         ; anstyp <- newVar kstar
         ; cs1 <- unify (tArrow ltyp anstyp) hint
         ; (_,cs2) <- check env (tArrow ltyp (tArrow rtyp anstyp)) oper
         ; (_,cs3) <- check env rtyp arg
         ; return (hint,cs1 ++ cs2 ++ cs3)
         }
    HsLeftSection arg oper ->  -- i.e. (3 +)
      do { ltyp <- newVar kstar
         ; rtyp <- newVar kstar
         ; anstyp <- newVar kstar
         ; cs1 <- unify (tArrow rtyp anstyp) hint
         ; (_,cs2) <- check env (tArrow ltyp (tArrow rtyp anstyp)) oper
         ; (_,cs3) <- check env ltyp arg
         ; return (hint,cs1 ++ cs2 ++ cs3)
         }
    HsRecConstr name fields -> error "not yet"
    HsRecUpdate arg fields -> error "not yet" 
    HsEnumFrom x ->                     -- [x ..] :: Enum a => [a]
      do { a <- newVar kstar
         ; cs1 <- unify hint (tlist a)
         ; (_,cs2) <- check env a x
         ; return (hint,(enum a) : cs1 ++ cs2)
         }
    HsEnumFromTo x y ->                 -- [x .. y] :: Enum a => a -> a -> [a]
      do { a <- newVar kstar
         ; cs0 <- unify hint (tlist a)
         ; (_,cs1) <- check env a x
         ; (_,cs2) <- check env a y
         ; return (hint,(enum a) : cs0 ++ cs1 ++ cs2)
         }
    HsEnumFromThen x y ->              -- [x, y ..] :  Enum a => a -> a -> [a] 
      do { a <- newVar kstar
         ; cs0 <- unify hint (tlist a)
         ; (_,cs1) <- check env a x
         ; (_,cs2) <- check env a y
         ; return (hint,(enum a) : cs0 ++ cs1 ++ cs2)
         }
    HsEnumFromThenTo x y z ->          -- [x,y .. z] :: Enum a => a -> a -> a -> [a] 
      do { a <- newVar kstar
         ; cs0 <- unify hint (tlist a)
         ; (_,cs1) <- check env a x
         ; (_,cs2) <- check env a y
         ; (_,cs3) <- check env a z
         ; return (hint,(enum a) : cs0 ++ cs1 ++ cs2 ++ cs3)
         }
    HsListComp stmt -> 
      do { let mtyp = tlistCon
         ; let m x = (S(HsTyApp mtyp x))
         ; a <- newVar kstar
         ; cs2 <- unify hint (m a)
         ; cs3 <- inferStmt gensym ngvars env mtyp a True stmt
         ; return (hint,cs2 ++ cs3)
         }
    HsExpTypeSig loc e qt -> 
      do { s <-  hsQual2Sch qt
         ; (cs1 :=> typ) <- instan s
         ; cs2 <- unify typ hint
         ; (_,cs3) <- check env typ e
         ; return (typ,cs1 ++ cs2 ++ cs3)
         }
    HsAsPat nm e -> error "pattern only"
    HsWildCard -> error "pattern only"
    HsIrrPat e -> error "pattern only"
    HsMetaBracket e ->  --  MetaHUGS extension <| exp |> 
      do { a <- newVar kstar
         ; cs1 <- unify hint (tcode a)
         ; (_,cs2) <- check env a e
         ; return (hint,cs1 ++ cs2)
         }
    HsMetaEscape e ->   --  MetaHUGS extansion ^exp 
      do { (_,cs1) <- check env (tcode hint) e
         ; return (hint,cs1)
         }


----------------------------------------------------------------------------------
-- inferStmt is used to infer the type of both Do stmts and list comprehensions
-- [ A | p <- e ; f ]  has the same structure as (do { P <- e; f ; A })
-- but the type rules differ slightly for both "A" and "f". We've parameterized
-- inferStmt to handle this

inferStmt :: Genfun a -> NGV a -> Env a -> Type a -> Type a -> Bool ->
           Stmt -> Im a Error [Pred (Type a)]
inferStmt gensym ngvars env mtyp lasttyp isListComp stmt = 
  let m x = (S(HsTyApp mtyp x)) in
  case stmt of
    HsGenerator p e next ->  --    p <- e ; next
      do { ptyp <- newVar kstar
         ; (_,cs2) <- infer gensym ngvars env (m ptyp) e
         ; (ngv2,env2,cs3) <- inferPat p ngvars env ptyp
         ; cs4 <- inferStmt gensym ngv2 env2 mtyp lasttyp isListComp next
         ; return (cs2 ++ cs3 ++ cs4)
         }        
    HsQualifier e next ->   --  e ; next
      do { typ <- if isListComp then return tBool else fmap m (newVar kstar)
         ; (_,cs2) <- infer gensym ngvars env typ e
         ; return cs2
         }
    HsLetStmt ds next ->   -- let ds ; next
      do { (ngv2,env2,cs2) <- inferDecls gensym ngvars env ds
         ; cs3 <- inferStmt gensym ngv2 env2 mtyp lasttyp isListComp next
         ; return (cs2 ++ cs3)
         }
    HsLast e -> do { (_,cs) <- infer gensym ngvars env lasttyp e; return cs }

 
inferAlt :: Genfun a -> NGV a -> Env a -> Type a -> Type a ->
           Alt -> Im a Error [Pred (Type a)]
inferAlt gensym ngvars env pathint bodyhint (HsAlt s p rhs ds) =
  do { (ngv2,env2,cs2) <- inferPat p ngvars env pathint
     ; (ngv3,env3,cs3) <- inferDecls gensym ngv2 env2 ds
     ; (_,cs4) <- 
          case rhs of
            (HsBody e) -> infer gensym ngv3 env3 bodyhint e
            (HsGuard ms) -> g ms
                where g [] = return (bodyhint,[])
                      g ((s,guard,e):ws) =
                          do { (_,cs4) <- infer gensym ngv3 env3 tBool guard
                             ; (t,cs5) <- infer gensym ngv3 env3 bodyhint e
                             ; (_,cs6) <- g ws
                             ; return (t,cs4 ++ cs5 ++ cs6)
                             }
     ; return (cs2 ++ cs3 ++ cs4)
     }


         
inferDecls :: Genfun a -> NGV a -> Env a -> 
            [HsDecl] -> Im a Error (NGV a,Env a,[Pred (Type a)])
inferDecls gensym ngvars env ds = return (ngvars,env,[])            

 
---------------------------------------------------------------------
-- The Parser produces HsQualType data structures, we must turn these
-- into Scheme data structures, while doing to we should kind-check
-- all the type information.

hsQual2Sch (HsQualType preds x) = scheme preds x
hsQual2Sch (HsUnQualType t) = scheme [] t

scheme :: [(HsName,HsName)] -> HsType -> Im a Error (Scheme Kind (U a Kind T))
scheme preds t = 
   do { newks <- sequence(map (const (newVar Sort)) names)
              -- A new Kind var for each of the free type variables in "t"
      ; let env = zip names newks -- Map each Type Var to its kind Var
      ; mainK <- kindOf (look env) t
      ; argKs <- sequence (map uaSortK_to_Kind newks)
      ; return (Sch argKs (map transPred preds) (trans sub t))
      }           
  where names = namesT t  -- All the free Type Variables in "t"
        sub = zipWith (\ t n -> (t,TGen n)) names [0..]
        trans sub (Typ (HsTyVar nm)) = look sub nm
        trans sub (Typ z) = (S(mapT (trans sub) z))
        transPred (cla,arg) = IsIn (show cla) [trans sub (Typ(HsTyVar arg))]

