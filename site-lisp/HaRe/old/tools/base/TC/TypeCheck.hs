-- $Id: TypeCheck.hs,v 1.39 2001/09/29 00:08:23 diatchki Exp $

module TypeCheck where

import TypeGenerics
import Monad(mapM, foldM)
import HsName
import HsTypeStruct
import Syntax
import InferenceMonad
import List(nub, find, intersect, (\\), lookup, union)
import ST
import SCC(bindingGroups)
import qualified Scope
import SyntaxUtil(getTyName)
------------------------------------------------------
infix 9 |->
infixr 3 +:

type Kind a    = GT K Sort (STRef a)
type Type a    = GT T (Kind a) (STRef a)
type NGV a     = [(HsName, Type a)]
type Env a     = [(HsName, Scheme a)]
type Constrs a = [Pred a]
type Ref a = (Int,STRef a (Maybe(Type a)))
type Ptr2 a = STRef a (Maybe(Type a))
type Genfun a = String -> IM a Error HsName 
type KindEnv a = [(HsName, GT K Sort (STRef a))]

data Pred a = IsIn HsName [Type a]
data Scheme a = Sch [Kind a] [Pred a] (Type a)
data Qual a x = [Pred a] :=> x
data Assump name a =  name :>: Scheme a


data Error = TCerror String

instance Show Error where
  show (TCerror s) = s

fails :: String -> IM a Error x
fails s = raise    (TCerror s)

unifyErr x y z = fails ((show x) ++"error in unification " ++ (show y)++", "++(show z))

instance Show (STRef a b) where
  show x = "?"
--------------------------------------------------------
newGensym :: IM a Error (Genfun a)
newGensym  =
    do { seed <- newRef (1::Int)
       ; let gensym s = do { n <- readVar seed
                           ; writeVar seed (n+1)
                           ; return (UnQual (s ++ (show n)))
                           }
         in return gensym
       }
       
  {-gensym s = do { n <- nextN   
                ; return (UnQual (s ++ (show n)))
                }
-}

------------------ Kind inference -----------------------

data Sort = Sort deriving Eq

kindA :: A K Sort () (STRef a) (IM a Error)
kindA =
    A { sameVarA = refEq
      , writeVarA = writeVar
      , readVarA = readVar
      , newVarA = newRef
      , nextA = nextN
      , zeroA = ()
      , unionA = const ()
      , genErrA = unifyErr
      , seqA = seqK
      , mapA = mapK
      , accA f = flip (accK f)
      , matchA = matchK
      , kindofA = const(return Sort)
      , samekindA = (==)
      }

refEq :: STRef a b -> STRef a b -> Bool
refEq x y = x==y

eqK :: Kind a -> Kind a -> Bool 

B{ unifyGT = unifyKind
 , equalGT = eqK
 , freshGT = newVarK 
 , pruneGT = pruneK
 , substGT = substK
 , genGT = genK } = makeUnify kindA

star = S Kstar
arrowK x y = S(Kfun x y)
predicate = S Kpred


instance Eq (Kind a) where
  (==) = eqK

-- Works on HSTypes while inferK2 works on (Type a)
inferK ::  [(HsName,Kind a)] -> Kind a ->  HsType -> IM a Error (Kind a)
inferK kenv k t =
  do { let f (nm,k) = do { v <- newVar k; return (nm,v)}
           h :: [(HsName,Type a)] -> HsType -> Type a
           h pairs (Typ (HsTyVar x)) = look pairs x
           h pairs (Typ x) = S(mapT (h pairs) x)
     ; pairs <- mapM f kenv
     ; inferK2 kenv k (h pairs t) 
     }


inferK2 :: [(HsName, Kind a)] -> Kind a -> (Type a) -> IM a Error (Kind a)         
inferK2 env hint t =
  do { t' <- prune t
     ; case t' of
         (TVar r k) -> return k
         (TGen n) -> return hint
         (S typ) ->
          case typ of
            (HsTyFun x y) ->
               do { x' <- inferK2 env star x
                  ; y' <- inferK2 env star y
                  ; unifyKind hint star
                  ; return hint
                  }
            (HsTyTuple ts) ->
               do { sequence (map (inferK2 env star) ts)
                  ; unifyKind hint star
                  ; return star
                  }
            (HsTyApp f x) ->
               do { a <- newVarK Sort
                  ; inferK2 env (S(Kfun a hint)) f
                  ; inferK2 env a x
                  ; return hint
                  }
            (HsTyVar nm) ->
               do { unifyKind hint (lookUpEnv env nm)
                  ; return hint
                  }
            (HsTyCon nm) ->  
               do { unifyKind hint (lookUpEnv env nm)
                  ; return hint
                  } }
                  
kindOf2 :: [(HsName,Kind a)] -> Type a -> IM a Error (Kind a)
kindOf2 envf x = do { hint <- newVarK Sort
                    ; inferK2 envf hint x
                    ; (ks,ts,x') <- genK (\ x -> return True) hint
                    ; k' <- substK (repeat star) x'
                    ; return k'
                    }
                    
getkind :: Type a -> IM a Error (Kind a)                    
getkind t = kindOf2 kenv0 t
  
  
--------------------------------------------------------------
typeA :: A T (Kind c) [Pred c] (STRef c) (IM c Error) 
typeA =
    A { sameVarA = refEq
      , writeVarA = writeVar
      , readVarA = readVar
      , newVarA = newRef
      , nextA = nextN
      , zeroA = []
      , unionA = concat
      , genErrA = unifyErr
      , seqA = seqT
      , mapA = mapT
      , accA = accT
      , matchA = matchT
      , kindofA = getkind
      , samekindA = eqK
      }
   
prune :: Type a -> IM a Error (Type a)
unify :: Type a -> Type a -> IM a Error [Pred a]
subst :: [Type a] -> Type a -> IM a Error (Type a)
B{ unifyGT = unify
 , matchGT = matchType
 , equalGT = teq
 , freshGT = newVar
 , colGT = col
 , occursGT = occursIn
 , pruneGT = prune
 , substGT = subst
 , genmapGT = gen
 } = makeUnify typeA    
 


match :: Type a -> Type a -> IM a Error Bool
match x y = (do { matchType x y; return True}) `handle` (\ _ -> return False)
  
    
unifyList xs ys =     
 if (length xs) == (length ys)  
    then do { xss <- mapM (uncurry unify) (zip xs ys)
            ; return (concat xss)
            }
    else fails "Lists not same length"
     
---------------------------------------------------------------

class Types t a where
  tv :: t -> IM a Error [Ref a]
  collapse :: t -> IM a Error t

  
instance Types (Type a) a where
    tv t = do { t' <- prune t
              ; case t' of
                 (TVar r k) -> return [r]
                 (S x) -> do { sh <- seqT (mapT tv x)
                            ; return $ nub (accT (++) sh [])
                            }
                 (TGen i) -> return []} 
    collapse t = col t
   
    
instance Types x a => Types [x] a where
  tv xs = do { xs' <- mapM tv xs; return(concat xs') }
  collapse ts = mapM collapse ts
  

instance Types (Pred a) a where
  tv (IsIn nm xs) = tv xs
  collapse (IsIn nm xs) = do {xs' <- collapse xs; return(IsIn nm xs')}
  
instance Types(Scheme a) a where
  tv (Sch ks ps t) = do {ps' <- tv ps; t' <- tv t; return(union ps' t')}
  collapse (Sch ks ps t) = 
     do {ps' <- collapse ps; t' <- collapse t; return(Sch ks ps' t')}

instance Types y a => Types (x,y) a where
  tv (x,y) = tv y
  collapse (x,y) = do {y' <- collapse y; return (x,y') }
  
----------------------------------------------------------------- 
  
class Instantiate x a where
  inst :: [Type a] -> x -> IM a Error x

instance Instantiate (Pred a) a where
  inst ts (IsIn nm xs) = do { xs' <- mapM (inst ts) xs; return (IsIn nm xs') }

instance Instantiate x a => Instantiate [x] a where
  inst ts xs = mapM (inst ts) xs

instance Instantiate (Type a) a where
  inst = subst    

--------------------------------------------------

class Template x a where
  fresh :: x -> IM a Error x

instance Template (Scheme a) a where
  fresh (Sch free cs t) =
    do { sub <- mapM newVar free
       ; t' <-  inst sub t 
       ; cs' <- sequence (map (inst sub) cs)
       ; return $ Sch free cs' t'
       }

instance Template (Inst a) a where
  fresh (Inst free ps p) =
    do { sub <- mapM newVar free
       ; p' <-  inst sub p 
       ; ps' <- sequence (map (inst sub) ps)
       ; return $ Inst free ps' p'
       }

--------------- Environment function and types --------------------------


extend f s t = (s,t) : f

lambdaExt :: [(name,Scheme a)] -> name -> Type a -> [(name,Scheme a)]
lambdaExt env vname vtyp = extend env vname (Sch [] [] vtyp)

lambdaExtTCE env vname vtyp  = extTrm vname (Sch [] [] vtyp) env


envf [] s = error ("variable not found: "++(show s)++"\n")
envf ((x,t):m) s = if x==s then t else envf m s

-------- Type constructors and types of literal constants ------------

starKind = S(Kstar)
arrowKind x y =S(Kfun x y)
predKind = S Kpred

tArrow x y = S(HsTyFun x y)
tTuple ts = S(HsTyTuple ts)
tInteger = S(HsTyCon (UnQual "Integer"))
tInt = S(HsTyCon (UnQual "Int"))
tChar = S(HsTyCon (UnQual "Char"))
tString = tlist tChar
tRational = S(HsTyCon (UnQual "Rational"))
tBool = S(HsTyCon (UnQual "Bool"))
tDouble = S(HsTyCon (UnQual "Double"))

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


---------------------------------------------------
-- Kind environment stuff

funkify [] env = env
funkify ((a,b):rest) env =  (a,b) +: (funkify rest env)



hsname |-> knd = (hsname,knd)

--(x,y) +: env =  \t -> if x == t then y else lookUpEnv env t
(x,y) +: env = (x,y) : env

--emptyKEnv x = error $ "unknown kinnd variable: " ++ (show x)
emptyKEnv  = []

lookUpEnv env t = 
  case List.lookup t env of
       Just b -> b
       Nothing -> error $ "Kind environment: " ++ (show t) ++ "not found!"


kenv0 = 
 (UnQual "Integer") |-> star +:
 (UnQual "Int") |-> star +: 
 (UnQual "Char") |-> star +: 
 (UnQual "Rational") |-> star +: 
 (UnQual "Bool") |-> star +: 
 (UnQual "Double") |-> star +:
 (UnQual "stringHash") |-> star +:
 (UnQual "CharHash") |-> star +:
 (UnQual "IntHash") |-> star  +:
 (UnQual "RationalHash") |-> star +:
 (UnQual "[]") |-> arrowK star star +:
 (UnQual "Q") |-> arrowK star star +:
 (UnQual "X") |-> arrowK star star +:
 (UnQual "W") |-> arrowK star star +:
 (UnQual "Num") |-> arrowK star predicate +: emptyKEnv 
 



------------------------ Predefined Class predicates ----------------

num x =   IsIn   (UnQual "Num")   [x] 
monad x = IsIn (UnQual "Monad")   [x]
enum x =  IsIn  (UnQual "Enum")   [x]


-----------------------------------------------------------------------------
-- This mimics the "Class Environments" Section (7.2) of Typing Haskell in 
-- Haskell. The differences are:
--  1) Class environments are lists rather than partial functions
--  1) Many functions are in the (IM a Error) Monad instead of the Maybe Monad
--  2) instead of Inst = Qual Pred
--     data INST a = INST [Kind] [Pred a] (Pred a)     
--     An instance is like a (Sch ks ps t), a fresh copy of an instance
--     can be made by applying the method "inst". this is usefull for 
--     determining if we have overlapping instances. We make fresh copies, 
--     and then we unify. Also like Schemes, things of type (Inst a) have a
--     normal form, because of this, and because (Inst a) should be TVar free
--     they can be compared for equality.

data Class a = Class HsName [HsName] [Inst a] 
  
data ClassEnv a  = ClassEnv { classList  :: [(HsName, Class a)]
                            , defaults :: [Type a] 
                            }
                            
data Inst a = Inst [Kind a] [Pred a] (Pred a)

instance Instantiate (Inst a) a where
  inst ts (Inst ks ps p) = 
     do { ps' <- (inst ts ps) 
        ; p' <- (inst ts p)
        ; return (Inst ks ps' p')
        }


instance Eq (Inst a) where
  (Inst ks1 ps1 p1) == (Inst ks2 ps2 p2) =
        listEq (==) ks1 ks2 && listEq (==) ps1 ps2 && p1 == p2
     
instance Eq (Pred a) where
  (IsIn c ts) == (IsIn d xs) = c==d && listEq teq ts xs
           
listEq eqf [] [] = True
listEq eqf (x:xs) (y :ys) = eqf x y && listEq eqf xs ys
listEq eqf _ _ = False


-----------------------------------------------------------------------

classes :: ClassEnv a -> HsName -> Maybe (Class a)
classes ce i = 
  case find ( \ (x,y) -> x==i) (classList ce) of
    Just (name,cl) -> Just cl
    Nothing -> Nothing

super :: ClassEnv a -> HsName -> [HsName]
super ce i = case classes ce i of Just (Class name sup insts) -> sup

insts :: ClassEnv a -> HsName -> [Inst a]
insts ce i = case classes ce i of Just (Class name sup its) -> its

defined :: Maybe a -> Bool
defined (Just _) = True
defined Nothing  = False

modify :: ClassEnv a -> HsName -> Class a -> ClassEnv a
modify ce i c = ce {classList =  (i,c)  :  classList ce }

initialEnv :: ClassEnv a
initialEnv = ClassEnv { classList  = [], defaults = [tInteger,tDouble] }   

type EnvTransformer a = ClassEnv a -> IM a Error (ClassEnv a)

infixr 5 <:>
(<:>) :: EnvTransformer a -> EnvTransformer a -> EnvTransformer a
(f <:> g) ce = do { ce' <- f ce; g ce' } 

                               {- ClassEnv a -> Maybe (ClassEnv a) -}     
addClass :: String -> [String] -> EnvTransformer a 
addClass i is ce 
  | defined (classes ce (UnQual i)) = 
      fails ("Adding class: "++(show i)++
            " to class environment failed. Class already defined. ") 
  | any (not . defined . (classes ce)) (map UnQual is) =  
      fails("Adding class: "++(show i)++
           " to class environment failed. Superclass not defined. ") 
  | otherwise = return (modify ce (UnQual i) (Class (UnQual i) (map UnQual is) [] ))

addCoreClasses :: EnvTransformer a
addCoreClasses 
 =   addClass "Eq" []
 <:> addClass "Ord" ["Eq"]
 <:> addClass "Show" []
 <:> addClass "Read" []
 <:> addClass "Bounded" []
 <:> addClass "Enum" []
 <:> addClass "Functor" []
 <:> addClass "Monad" []

addNumClasses :: EnvTransformer a
addNumClasses 
 =   addClass "Num" ["Eq","Show"]
 <:> addClass "Real" ["Num","Ord"]
 <:> addClass "Fractional" ["Num"]
 <:> addClass "Integral" ["Real","Enum"]
 <:> addClass "RealFract" ["Real","Fractional"]
 <:> addClass "Floating" ["Fractional"]
 <:> addClass "RealFloat" ["RealFract","Floating"]
 
 <:> addInst (Inst [] [] (IsIn (UnQual "Num") [tInteger]))

ce0 = (addCoreClasses <:> addNumClasses) initialEnv

------------------------------------------------------------------


overlap :: Pred a -> Pred a -> IM a Error Bool
overlap (IsIn c ts1) (IsIn d ts2) = 
  if c==d
     then (do { unifyList ts1 ts2; return True}) `handle` (\ _ -> return False)
     else return False

addInst :: Inst a -> EnvTransformer a
addInst (x @ (Inst ks ps (p @ (IsIn i _)))) ce
  | not (defined (classes ce i)) = fails ("No class: "++(show i)++", for instance")
  | otherwise = do { Inst _ _ p' <- fresh x
                   ; qs <- sequence (map getPred its)  -- the predicates (without qualifiers)
                   ; lap <- fmap or (sequence (map (overlap p') qs))
                   ; if lap
                        then fails ("Overlapping instance for: "++(show i)++".")
                        else return(modify ce i c)
                   }
 where its = insts ce i                    -- the instances of i
       getPred (x @(Inst ks ps q)) = do { Inst _ _ q' <- fresh x; return q' }
       c = Class i (super ce i) (x:its)    -- the new class with additional instance
      
bySuper :: ClassEnv a -> Pred a -> [Pred a]
bySuper ce (p @ (IsIn cname ts)) =
  p : concat[bySuper ce (IsIn c' ts) | c' <- super ce cname]


lift :: (Type a -> Type b -> IM c Error d) -> Pred a -> Pred b -> IM c Error [d]
lift m (IsIn c1 ts1) (IsIn c2 ts2) =
  if (c1==c2) && (length ts1) ==(length ts2)
     then sequence (zipWith m ts1 ts2)
     else fails "classes do not match"

matchPred :: Pred a -> Pred a -> IM a Error Bool
matchPred x y = fmap and (lift match x y)

byInst :: Pred a -> Inst a -> IM a Error (Maybe [Pred a])
byInst p (x @ (Inst ks ps h)) =
  do { Inst _ ps' h' <- fresh x
     ; b <- matchPred h' p
     ; if b
          then return (Just ps')
          else return Nothing
     }

reducePred :: ClassEnv a -> Pred a -> IM a Error (Maybe [Pred a])
reducePred ce (p @ (IsIn c ts)) =
  let instances = (insts ce c)
      first [] = return Nothing
      first (i:is) = 
           do { m <- byInst p i
              ; case m of
                  Just ps -> return(Just ps)
                  Nothing -> first is }
  in first instances
 
anyM p xs = fmap or (sequence (map p xs))
 

entail :: ClassEnv a -> [Pred a] -> Pred a -> IM a Error Bool
entail ce ps p =
  do { let preconditions = (map (bySuper ce) ps)  -- all possible preds => by ps
           alreadythere = (any (p `elem`) preconditions)
     ; if alreadythere
          then return True
          else do { m <- reducePred ce p
                  ; case m of
                      Nothing -> return False
                      Just qs -> do { bs <- sequence (map (entail ce ps) qs)
                                    ; return (and bs)
                                    } } }
                                    
                                    
inHnf (IsIn c ts) = all hnf ts
  where hnf (TVar _ _) = True
        hnf (S(HsTyApp x _)) = hnf x
        hnf (S _) = False
        hnf (TGen n) = False

toHnf :: ClassEnv a -> Pred a -> IM a Error [Pred a]
toHnf ce p =
  if inHnf p
     then return [p]
     else do { m <- reducePred ce p
             ; case m of
                 Nothing -> fails "context reduction"
                 Just ps -> toHnfs ce ps
             }
             
toHnfs ce ps = fmap concat (mapM (toHnf ce) ps)

simplify :: ClassEnv a -> [Pred a] -> [Pred a] -> [Pred a] 
simplify ce rs [] = rs
simplify ce rs (p:ps) = simplify ce (p:(rs \\ qs)) (ps \\ qs)
  where qs = bySuper ce p
        rs \\ qs = [ r | r <- rs, r `notElem` qs]
        

numClasses :: [HsName]       
numClasses = 
 map UnQual ["Num","Integral","Floating","Fractional","Real","RealFloat","RealFrac"]

stdClasses :: [HsName]       
stdClasses = 
 map UnQual ["Eq","Ord","Show","Read","Bounded","Enum","Ix","Functor"
            ,"Monad","MonadPlus"] ++
 numClasses
 
 
defs     :: ClassEnv a -> Ref a -> [Pred a] -> IM a Error [Type a]
defs ce v qs =
   if (all (same v) ts) &&
      (all (`elem` stdClasses) clnames) &&
      (any (`elem` numClasses) clnames)
      then fmap concat(sequence (zipWith f (defaults ce) (repeat clnames)))
      else return []
 where clnames = [ c | (IsIn c t) <- qs ]
       ts = [ t | (IsIn c [t]) <- qs ] -- DON"T KNOW if this translates to MPTC
       same (n,v) (TVar (m,u) k) = v==u
       same v _ = False
       f t [] = return []
       f t (c:cs) = do { b <- entail ce [] (IsIn c [t])
                       ; if b then do { ts <- f t cs; return(t:ts) }
                              else f t cs
                       }



ambig :: ClassEnv a -> [Ref a] -> [Pred a] -> IM a Error [(Ref a,[Pred a],[Type a])]
ambig ce vs ps =
  do { psvss <- sequence(map tv ps) -- [[ vars ]]
     ; let psvs = concat psvss      -- [ vars ] all of them in any of the ps
           ambigvs = psvs \\ vs     -- vars in ps but not in vs
           getqs v [] = []
           getqs v ((free,p):xs) = if elem v free then p:(getqs v xs) else getqs v xs
           f v = let qs = getqs v (zip psvss ps)
                 in do { ts <- (defs ce v qs)
                       ; ts' <- mapM collapse ts
                       ; return (v,qs,ts') }
     ; sequence (map f ambigvs)
     }

useDefaults :: String -> ClassEnv a -> [Ref a] -> [Pred a] -> IM a Error [Pred a]
useDefaults names ce vs ps =
  do { ams <- ambig ce vs ps
     -- [(v,ps,ts)]  "v" can be resolved to any of the "ts", which then cancels the "ps"
     ; let tss = [ts | (v,qs,ts) <- ams]      
           ps' = [p | (v,qs,ts) <- ams, p <- qs]
           fix ((n,v),ps,ts) = writeVar v (Just (head ts))   
     ; if any null tss -- if any "v" can't be resolved by some "t" we have to fail
          then fails "ambiguity"
          else do { cs <- mapM fix ams
                  ; newps <- collapse ((ps \\ ps'))
                  ; return newps -- subtract the cancelled ps
                  }
     }
     

partitionM p xs = select xs 
  where select [] = return ([],[])
        select (x:xs) = 
           do { (ys,zs) <- select xs
              ; b <- p x
              ; if b then return (x:ys,zs) else return (ys,x:zs)
              }

split :: ClassEnv a -> [Ref a] -> [Pred a] -> IM a Error ([Pred a],[Pred a])
split ce fs ps =
  do { ps2 <- toHnfs ce ps
     ; let ps3 = simplify ce [] ps2
     ; partitionM p ps3
     }
  where p ps = do { free <- tv ps; return(all (`elem` fs) free) }

reduce :: String -> ClassEnv a -> [Ref a] -> [Ref a] -> [Pred a] 
          -> IM a Error ([Pred a],[Pred a])  
reduce names ce fs gs ps = 
  do { (ds,rs) <- split ce fs ps
     ; rs' <- useDefaults names ce (fs ++ gs) rs
     ; return(ds,rs')
     }
     
----------------------------------------------------------------------------


type NGVars a = [(HsName,Type a)]

emptyNGVars :: NGVars a
emptyNGVars = []

extendNGVars :: HsName -> Type a -> NGVars a -> NGVars a
extendNGVars s t ngvars = (s,t):ngvars

generic :: NGVars a -> Ref a  -> IM a Error Bool 
generic ngvars (_,v) = do { b <- occursInList v ngvars; return (not b) }
     where occursInList v l =
            do { bools <- mapM (\ (a,b) -> occursIn v b) l
               ; return (or bools)
               }
       

-------------------------------------------------------------------------

-- unArrow [p1,p2,p3] (t1 -> t2 -> t3 -> t4) ---> (t4,[(p1,t1),(p2,t2),(p3,t3)])
unArrow :: [HsPat] -> Type a -> IM a Error (Type a,[(HsPat,Type a)])
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


patExt :: HsPat -> Type a ->TEnv a -> IM a Error (Type a,NGV a,[Pred a])
patExt (Pat p) typ env =
  case p of
   HsPId(HsVar name) -> return (typ,[(name,typ)],[])
   HsPId(HsCon name) ->
       case lookTrmOpt env name of
            Nothing -> fails $ "Data constructor " ++ (show name) ++ " not defined!!!"
            Just (scheme @ (Sch tvars preds typ)) -> 
                   do { newVars <- mapM (\k -> newVar k) tvars
                      ; t' <- inst newVars typ
                      ; ps <- mapM (inst newVars) preds
                      ; return (t',[],ps) }
   (HsPLit (HsInt _)) ->  
      do   { nv <- newVar starKind
           ; cs <- unify nv typ
           ; return (nv, [], [(num nv)]++cs) }
   (HsPLit l) -> 
      do { let t = litTyp l
         ; cs <- unify t typ
         ; return (t,[],cs) 
         }
   (HsPNeg x) -> error "whats this?"
   (HsPInfixApp x n y) -> patExt (Pat(HsPApp (getHSName n) [x,y])) typ env 
   (HsPApp nm ps) -> 
      do { Sch _ cs1 ctyp <- fresh (lookTrm env nm)
         ; (t,patTypeList) <- unArrow ps ctyp
         ; cs2 <- unify t typ
         ; (ts2,env2,cs3) <- patExtTup patTypeList env 
         ; return (t,env2,cs1 ++ cs2 ++ cs3)
         }
   (HsPTuple ps) ->
      do { ts <- sequence (map (\ x -> (newVar starKind)) ps)
         ; cs2 <- unify (tTuple ts) typ
         ; (ts,ngv3,cs3) <- patExtTup (zip ps ts) env
         ; return (tTuple ts,ngv3,cs2 ++ cs3)
         }         
   (HsPList ps ) -> 
      do { elemtyp <- newVar starKind
         ; (listtyp,ngv2,cs) <- patExtList ps elemtyp env []
         ; cs2 <- unify listtyp (tlist elemtyp)
         ; cs3 <- unify typ listtyp
         ; return (listtyp,ngv2,cs ++ cs2++ cs3)
         }        
   (HsPParen x) -> patExt x typ env
   (HsPRec n pairs) -> error "not yet"
   (HsPRecUpdate nm pairs) -> error "not yet"
   (HsPAsPat name x) ->
      do { (t,ngv1,cs1) <- patExt x typ env
         ; return (t,(name,t):ngv1,cs1)
         }
   (HsPWildCard) -> do { t <- newVar starKind 
                       ; cs <- unify typ t
                       ; return (t,[],cs) }
   (HsPIrrPat x) -> patExt x typ env

inferPats :: [HsPat] -> NGV a -> TEnv a ->  
               IM a Error ([Type a],NGV a,TEnv a,[Pred a])
inferPats ps ngvars env =
  do { pairs <- sequence (map (\ p -> do { t <- newVar starKind; return (p,t) }) ps)
     ; (t1,ngv1,cs1) <- patExtTup pairs env
     ; return (t1,ngv1 ++ ngvars,g ngv1 env,cs1)
     }  where g [] env = env
              g ((v,t):more) env = lambdaExtTCE (g more env) v t 
  
inferPat p ngvars env hint =
  do { (t,ngv1,cs1) <- patExt p hint env
     ; unify t hint
     ; return (ngv1 ++ ngvars,g ngv1 env,cs1)
     }  where g [] env = env
              g ((v,t):more) env = lambdaExtTCE (g more env) v t


-------------------------------------------------------------

infer :: Genfun a -> NGV a -> TEnv a -> Type a ->
            HsExp -> IM a Error (Type a,[Pred a])            
infer gensym ngvars env hint (exp @ (Exp e)) =
  let check env hint x = infer gensym ngvars env hint x 
  in
  case e of
    HsId(HsVar nm) -> 
      do { Sch _ cs t <- fresh (lookTrm env nm)
         ; cs2 <- unify t hint
         ; return (t,cs ++ cs2)
         }
    HsId(HsCon nm) -> 
      do { Sch _ cs t <- fresh (lookTrm env nm)
         ; cs2 <- unify t hint
         ; return (t,cs++cs2)
         }
    HsLit (HsInt _) -> 
      do { nt <- newVar starKind
         ; unify nt hint
         ; return (nt, [num nt]) }
    HsLit n -> 
      do { let t = litTyp n
         ; cs <- unify t hint
         ; return (t,cs)
         }         
    HsInfixApp x (HsVar f) y -> check env hint (hsApp (hsApp (hsEVar f)  x) y)
    HsInfixApp x (HsCon f) y -> check env hint (hsApp (hsApp (hsECon f)  x) y)
    HsApp f x ->
      do { xtyp <- newVar starKind
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
         ; result <- newVar starKind
           -- f [t1,t2,t3] r --> (t1 -> t2 -> t3 -> r)
         ; let f [] rng = rng
               f (t:ts) rng = tArrow t (f ts rng)
               ans = f ptyps result
         ; (_,cs2) <- infer gensym ngv2 env2 result x
         ; cs3 <- unify ans hint
         ; return (ans,cs ++ cs2 ++ cs3)
         }  
    HsLet ds e -> 
      do { (ngv2,env2,cs2) <- inferDs gensym ngvars env ds
         ; (etyp,cs3)  <- infer gensym  ngv2 env2 hint e
         ; return (etyp,cs2++cs3)
         }
    HsIf x y z -> 
      do { t <- newVar starKind
         ; (_,cs1) <- check env tBool x
         ; (_,cs2) <- check env t y
         ; (_,cs3) <- check env t z
         ; unify t hint
         ; return (t,cs1 ++ cs2 ++ cs3)
         }    
{-    HsCase e alts -> 
      do { argtyp <- newVar starKind
         ; (ptyp,cs1) <- check env argtyp e
         ; csAll <- mapM (inferAlt gensym ngvars env ptyp hint) alts
         ; return (hint, cs1 ++ concat csAll)
         } 
-}

    HsDo stmt -> 
      do { mtyp <- newVar (arrowKind starKind starKind)
         ; let m x =  (S(HsTyApp mtyp x))
         ; a <- newVar starKind
         ; cs2 <- unify hint (m a)
         ; cs3 <- inferStmt gensym ngvars env mtyp (m a) False stmt
         ; return (hint,(monad mtyp) : cs2 ++ cs3)
         }
    HsTuple xs -> 
      do { pairs <- sequence (map (\ x -> do { t <- newVar starKind; return (t,x) }) xs)
         ; let tupletyp = tTuple(map fst pairs)
         ; cs1 <- unify hint tupletyp
         ; ts <- mapM (uncurry (check env)) pairs
         ; return (hint,foldr (\ (t,c) cs -> c ++ cs) cs1 ts)
         }
    HsList xs -> 
      do { elemtyp <- newVar starKind
         ; cs1 <- unify hint (tlist elemtyp)
         ; pairs <- mapM (check env elemtyp) xs
         ; return (hint,foldr (\ (t,c) cs -> c ++ cs) cs1 pairs)
         }
    HsParen x -> check env hint x
    HsRightSection op arg ->  -- i.e.  (+ 3) }
      do { ltyp <- newVar starKind
         ; rtyp <- newVar starKind
         ; anstyp <- newVar starKind
         ; cs1 <- unify (tArrow ltyp anstyp) hint
         ; (_,cs2) <- check env (tArrow ltyp (tArrow rtyp anstyp)) (hsId op)
         ; (_,cs3) <- check env rtyp arg
         ; return (hint,cs1 ++ cs2 ++ cs3)
         }
    HsLeftSection arg op ->  -- i.e. (3 +)
      do { ltyp <- newVar starKind
         ; rtyp <- newVar starKind
         ; anstyp <- newVar starKind
         ; cs1 <- unify (tArrow rtyp anstyp) hint
         ; (_,cs2) <- check env (tArrow ltyp (tArrow rtyp anstyp)) (hsId op)
         ; (_,cs3) <- check env ltyp arg
         ; return (hint,cs1 ++ cs2 ++ cs3)
         }
    HsRecConstr name fields -> error "not yet"
    HsRecUpdate arg fields -> error "not yet" 
    HsEnumFrom x ->                     -- [x ..] :: Enum a => [a]
      do { a <- newVar starKind
         ; cs1 <- unify hint (tlist a)
         ; (_,cs2) <- check env a x
         ; return (hint,(enum a) : cs1 ++ cs2)
         }
    HsEnumFromTo x y ->                 -- [x .. y] :: Enum a => a -> a -> [a]
      do { a <- newVar starKind
         ; cs0 <- unify hint (tlist a)
         ; (_,cs1) <- check env a x
         ; (_,cs2) <- check env a y
         ; return (hint,(enum a) : cs0 ++ cs1 ++ cs2)
         }
    HsEnumFromThen x y ->              -- [x, y ..] :  Enum a => a -> a -> [a] 
      do { a <- newVar starKind
         ; cs0 <- unify hint (tlist a)
         ; (_,cs1) <- check env a x
         ; (_,cs2) <- check env a y
         ; return (hint,(enum a) : cs0 ++ cs1 ++ cs2)
         }
    HsEnumFromThenTo x y z ->          -- [x,y .. z] :: Enum a => a -> a -> a -> [a] 
      do { a <- newVar starKind
         ; cs0 <- unify hint (tlist a)
         ; (_,cs1) <- check env a x
         ; (_,cs2) <- check env a y
         ; (_,cs3) <- check env a z
         ; return (hint,(enum a) : cs0 ++ cs1 ++ cs2 ++ cs3)
         }
    HsListComp stmt -> 
      do { let mtyp = tlistCon
         ; let m x = (S(HsTyApp mtyp x))
         ; a <- newVar starKind
         ; cs2 <- unify hint (m a)
         ; cs3 <- inferStmt gensym ngvars env mtyp a True stmt
         ; return (hint,cs2 ++ cs3)
         }
    HsExpTypeSig loc e qt -> 
      do { Sch _ cs1 typ <-  hsQual2freshSch qt
         ; cs2 <- unify typ hint
         ; (_,cs3) <- check env typ e
         ; return (typ,cs1 ++ cs2 ++ cs3)
         }
    HsAsPat nm e -> error "pattern only"
    HsWildCard -> error "pattern only"
    HsIrrPat e -> error "pattern only"
    {-
    HsMetaBracket e ->  --  MetaHUGS extension <<| exp |> 
      do { a <- newVar starKind
         ; cs1 <- unify hint (tcode a)
         ; (_,cs2) <- check env a e
         ; return (hint,cs1 ++ cs2)
         }
    HsMetaEscape e ->   --  MetaHUGS extansion ^exp 
      do { (_,cs1) <- check env (tcode hint) e
         ; return (hint,cs1)
         }
    -}


isValueDecl (Dec d) =  
 case d of 
      HsPatBind _ _ _ _ -> True
      HsFunBind _ _     -> True
      _                 -> False

isTypeDecl (Dec d) = 
 case d of 
    HsTypeDecl _ _ _ -> True
    HsDataDecl _ _ _ _ _ -> True
    HsPrimitiveTypeDecl _ _ _ -> True
    _                         -> False

isClassInstDecl (Dec d) = 
  case d of 
   HsClassDecl _ _ _ _ -> True
   HsInstDecl _ _ _ _  -> True
   HsDefaultDecl _ _   -> True
   _                   -> False


--------------------------------------------------------------------
-- InferDs, first breaks the [HsDecl] into strongly connected binding
-- groups, then types each set separately using inferBG
inferDs :: Genfun a -> NGV a -> TEnv a -> [HsDecl] -> IM a Error (NGV a,TEnv a, Constrs a)
inferDs gensym ngv env ds = 
 let valueDs = filter isValueDecl ds
     typeDs  = filter isTypeDecl  ds
     (groups,_)  = bindingGroups valueDs
     (typeGroups,cyclicSynonyms) =  bindingGroups typeDs
     f (ngv,env,cs) ds = do { (n,e,c) <- inferBG gensym ngv env ds; return(n,e,c++cs)}
     g (env)   ds = do {  env' <- inferDataTypes gensym env ds
                       ; return env' }
 in do { if cyclicSynonyms then fails "Cyclic type synonyms" else return ()
       ; e <- (foldM g env typeGroups)
       ; foldM f (ngv,e,[]) groups
       }

------------------------------------------------------------------
-- Section 4.5.2 of the Haskell report states that all constraints
-- resulting from typing a single binding group are collected together
-- to form the context of the type for each name bound in the binding
-- group. Thus given a binding group we should construct a delta env
-- with a binding for each name, and a common set of contraints.

pr2 s x = do { x' <- x; pr s x'}

dataTypeName sloc (Typ t) = 
 case t of 
    HsTyVar n   -> return n
    HsTyApp a b -> dataTypeName sloc a
    HsTyCon n   -> return n
    _  -> fails $ show sloc ++ "Error in type pattern: ill formed. "

dataTypeArgs sloc (Typ t) = 
 case t of 
     HsTyVar n   -> return [n]
     HsTyApp a b -> dataTypeArgs sloc b
     HsTyCon _   -> return []
     _  -> fails $ show sloc ++ "Error in type pattern: ill formed. "


inferDataTypes gensym env []  = return env
inferDataTypes gensym env ds = 
  do  { let (freef, envf) = Scope.freeD ds
            freeVars = freef []
      ; vs <- mapM (\_ -> newVarK Sort) freeVars 
      ; pr "In binding group; type constructors" freeVars
      ; env' <- return $ foldr (.) id (zipWith extTconstr freeVars vs) env0
      ; r <- mapM (inferDataType gensym  env') ds
      ; return (foldr (+|+) env r ) 
      }

     

-- data (Q x, P y) => T x y = C x y | D [y] x
--  tpat = T x y
--  ctxt = [Q x,P y]
--  C :: Sch [*,*] (Q #0,P #1) (#0 -> #1 -> T #0 #1)
--  D :: Sch [*,*] (Q #1,P #0) ([#0] -> #1 -> T #1 #0)
inferDataType gensym env (Dec d) = 
 case d of 
   HsDataDecl sloc ctxt (tcon:targs) consdecls derivs  -> 
    do { pr "In Infer Data with " ((show tcon)++" -- "++(show targs))
       ; let { tpat  = foldl hsTyApp tcon targs }
       ; pairs <- mapM (\ nm -> do { k <- newVarK Sort; return(nm,k)}) 
                   (map getTyName targs)
       ; pr "pairs" pairs
       ; envd <- return $ (foldr (.) id (map (\ (nm,k) -> extTconstr nm k ) pairs)) env
       ; let kindCheck k x = (pr "in kindcheck " (show x)) >> inferK (getKindEnv envd) k x
             constrs (HsConDecl sloc consname btypes) =
               do { let types = (map unBang btypes)
                  ; pr "constr is " ((show consname) ++" with "++(show (length types)))
                  ; pr ("constr arity for" ++ (show consname)++": ") (length types)
                  ; mapM (kindCheck star) types
                  ; return (consname, foldr hsTyFun tpat types)
                  }
       ; kindCheck star tpat
       ; mapM_ (kindCheck predicate) ctxt
       ; delta <- mapM constrs consdecls
       ; pr "delta" delta
       ; let delta2 = foldr (.) id (map (\ (nm,sch) -> extTrm nm sch) (map (hsType2Scheme (lookTconstr envd) ctxt) delta)) env0
       ; return (delta2 +|+ env)
       }
   HsTypeDecl sloc (constr : args) body -> return(env)
   other -> error "not implemented yet"
         
hsType2Scheme kenvd ps (nm,t) =
  let free (Typ (HsTyVar nm)) ans = union [nm] ans
      free (Typ t) ans = accT free t ans
      vars = free t []
      sigma = zipWith (\ n nm -> (nm,TGen n)) [0..] vars
      t' = rebuild sigma t
      ps' = map (type2pred (rebuild sigma)) ps
  in (nm,Sch (map kenvd vars) ps' t')
  

unBang (HsBangedType a) = a
unBang (HsUnBangedType a)  =a 
 
 
------------------------------------------------------------------------------ 
extBGmono :: [HsDecl] -> IM a Error (NGV a,TEnv a,Constrs a,[(Type a,HsDecl)])
extBGmono ds = foldM extB ([],env0,[],[]) ds 
  where extB (ngvars,env,cs,tds) (dec @ (Dec d)) =
          case d of
            HsPatBind s pat e ds ->
               do { ptype <- newVar starKind
                  ; (ngv2,env2,cs2) <- inferPat pat ngvars env ptype
                  ; return(ngv2,env2,cs2++cs,(ptype,dec):tds)
                }
            HsFunBind s matches ->
               do { let getname ((HsMatch sloc name ps rhs ds):_)  = name
                        name = getname matches
                  ; ftype <- newVar starKind
                  ; let env2 = lambdaExtTCE env name ftype
                  ; return((name,ftype):ngvars,env2,cs,(ftype,dec):tds)
                  }

    
inferBG :: Genfun a -> NGV a -> TEnv a -> [HsDecl] -> IM a Error (NGV a,TEnv a, Constrs a)
inferBG gensym ngv env [] = return(ngv,env,[])

inferBG gensym ngv env ds =
  do { (ngvDelta,envDelta,cs,tds) <- extBGmono ds 
     ; let names = showl (map show (map fst  ngvDelta))  ""
     ; cs2 <- foldM    (inferEach gensym (ngvDelta++ngv) (envDelta +|+ env)) cs tds
     ; ps' <- sequence (map collapse cs2)
     ; ts' <- mapM collapse (map snd ( ngvDelta))
     ; fs <- fmap concat (sequence (map (\ (name,t) -> tv t) ngv))
     ; vss <- mapM tv ts'
     ; let inEveryT = foldr1 intersect vss
           gs = (foldr List.union [] vss) \\ fs  -- In infered types, but not env
       -- at this point ps' holds all the constraints resulting from typing
       -- the whole binding group. envDelta holds an env with monomorphic types for
       -- just the names bound by the binding group, and ngvDelta pairs just those
       -- names with their types.
     ; ce <- ce0 
     ; (deferred,retained) <- reduce names ce fs inEveryT ps'
     ; let generic x = return True --(x `elem` gs) 
           genSch (name,t) = do { sch <- quant generic (retained :=> t)
                             ; return (name,sch) }
           getngv (x,Sch ks ps t) = (x,t)
     ; d2 <- mapM genSch ngvDelta 
     ; delta2 <- return $ (foldr (.) id (map (uncurry extTrm) d2) (E [] [] []))
     ; return (map getngv (getTermEnv delta2) ++ ngv,delta2 +|+ env,deferred)
     } 


quant :: (Ptr2 a -> IM a Error Bool) -> Qual a (Type a) -> IM a Error (Scheme a)
quant generic (x @ (preds :=> typ)) =
  do { free <- newRef []
     ; z <- col typ
     ; let genPred (IsIn c ts) =
             do {ts' <- mapM (gen generic free) ts
                ; return (IsIn c ts') }
     ; typ' <- gen generic free typ
     ; preds' <- mapM genPred preds
     ; theta <- readVar free
     ; x <- col typ'
     ; return $ Sch (map (\ (t,_,k) -> k) (reverse theta)) preds' x
     }
          

inferEach gensym ngv env cs (t,Dec d) =
   do { 
        case d of
         HsPatBind s pat rhs ds -> 
            do { (ngv1,env1,cs1) <- inferDs gensym ngv env ds
               ; cs2 <- inferRhs ngv1 env1 t rhs
               ; return(cs1++cs2)
               }
         HsFunBind s matches -> foldM (infermatch t) cs matches
         other -> error "Only PatBind and FunBind allowed in inferEach"
      }
 where inferRhs ngv env hint (HsGuard gs) = foldM (inferGuard ngv env hint) cs gs
       inferRhs ngv env hint (HsBody e) = 
         do { (etyp,cs2) <- infer gensym ngv env hint e
            ; return(cs2++cs) }     
       inferGuard ngv env hint cs (srloc,guard,body) =
         do { (_,cs2) <- infer gensym ngv env tBool guard
            ; (_,cs3) <- infer gensym ngv env hint body
            ; return (cs3++cs2++cs) }
       infermatch hint cs (HsMatch sloc name ps rhs ds) = 
         do { (ts,ngv1,env1,cs1) <- inferPats ps ngv env
            ; (ngv2,env2,cs2) <- inferDs gensym ngv1 env1 ds
            ; range <- newVar starKind
            ; cs3 <- unify hint (foldr tArrow range ts)
            ; cs4 <- inferRhs ngv2 env2 range rhs
            ; return(cs4++cs3++cs2++cs1++cs)
            }


------------------------------------------------------------------
----------------------------------------------------------------------------------
-- inferStmt is used to infer the type of both Do stmts and list comprehensions
-- [ A | p <- e ; f ]  has the same structure as (do { P <- e; f ; A })
-- but the type rules differ slightly for both "A" and "f". We've parameterized
-- inferStmt to handle this

inferStmt :: Genfun a -> NGV a -> TEnv a -> Type a -> Type a -> Bool ->
           HsStmtR -> IM a Error [Pred a]
inferStmt gensym ngvars env mtyp lasttyp isListComp stmt = 
  let m x = (S(HsTyApp mtyp x)) in
  case stmt of
    HsGenerator p e next ->  --    p <- e ; next
      do { ptyp <- newVar starKind
         ; (_,cs2) <- infer gensym ngvars env (m ptyp) e
         ; (ngv2,env2,cs3) <- inferPat p ngvars env ptyp
         ; cs4 <- inferStmt gensym ngv2 env2 mtyp lasttyp isListComp next
         ; return (cs2 ++ cs3 ++ cs4)
         }        
    HsQualifier e next ->   --  e ; next
      do { typ <- if isListComp then return tBool else fmap m (newVar starKind)
         ; (_,cs2) <- infer gensym ngvars env typ e
         ; return cs2
         }
    HsLetStmt ds next ->   -- let ds ; next
      do { (ngv2,env2,cs2) <- inferDs gensym ngvars env ds
         ; cs3 <- inferStmt gensym ngv2 env2 mtyp lasttyp isListComp next
         ; return (cs2 ++ cs3)
         }
    HsLast e -> do { (_,cs) <- infer gensym ngvars env lasttyp e; return cs }

 
---------------------------------------------------------------------
-- The Parser produces HsQualType data structures, we must turn these
-- into Scheme data structures, while doing to we should kind-check
-- all the type information.

hstype2Type :: HsType -> Type a
hstype2Type (Typ x) = S(mapT hstype2Type x) 

-- Takes [ HsType ] representing qualifying predicates and a (HsType)
-- and produces fresh Scheme for that annotation. used like
-- ( x :: (P,Q) => t )

hsQual2freshSch:: HsTypeId HsType [HsType] -> IM a Error (Scheme a)
hsQual2freshSch x = f (preds x) (types x)
  where preds (TypeQual ps x) = ps
        preds (TypeUnQual x) = []
        types (TypeQual ps x) = x
        types (TypeUnQual x) = x
        f preds x =
          do { let names = freeNames [] x
             ; let g x = do { v <- newVar starKind; return(x,v) }
             ; sub <- mapM g names
             ; let x' = rebuild sub x
                   preds' = map (type2pred (rebuild sub)) preds
             ; return(Sch [] preds' x')
             }


-----------------------------------------------------------------
-- Helper functions for turning HsType into (Type a) and (Pred a)

type2pred :: (HsType -> Type a) -> HsType -> Pred a
type2pred g (Typ(HsTyApp (Typ(HsTyVar f)) x)) = IsIn f [g x]
type2pred g (Typ(HsTyApp (Typ(HsTyCon f)) x)) = IsIn f [g x]
type2pred g (Typ(HsTyApp f x)) = IsIn h ((g x): ys)
     where IsIn h ys = type2pred g f
type2pred g x = error ("type2pred dies: " ++(show x))
   
freeNames :: [HsName] -> HsType -> [HsName]
freeNames bound (Typ x) =
  case x of
    HsTyVar n -> if elem n bound then [] else [n]
    x -> accT f x []
       where f x ans = union (freeNames bound x) ans

rebuild :: [(HsName,Type a)] -> HsType -> Type a
rebuild sub (Typ x) =
  case x of
    HsTyVar n -> case find (\ (x,y) -> x==n) sub of
                   Just(_,v) -> v
                   Nothing -> error "unknown type variable in signature"
    x -> S(mapT (rebuild sub) x)

   
look ((y, e):ys) x = if x == y then e else look ys x
look [] x = error  "empty list in look"

--------- Show Instances ----------------------------------
 
                             
instance Show(Type a) where 
  showsPrec n (S x) = shows x
  showsPrec n (TGen m) = showString "%" . shows m
  showsPrec n (TVar (m,r) k) = showString ("("++(show m)++",?)")

instance Show(Pred a) where
  showsPrec m (IsIn n ts) = 
     showString "(" . showsPrec m n . showString " " . shl ts . showString ")" 
   

shl [] ss = ss
shl [x] ss = (showsPrec 0 x . showString " ") ss
shl (x:xs) ss = showsPrec 0 x ( showString ", " (shl xs ss))


showl [] ss = ss
showl [x] ss = showString (x++" ") ss
showl (x:xs) ss = showString (x++", ") (showl xs ss)

instance Show (Scheme a) where
  --show (Sch x p t) = "(all " ++ (showString (showList (nums x)"") "") ++"." ++ (show p) ++ " => " ++ (show t) ++ ")"  
  showsPrec n (Sch x p t) =  
        showString "(all " . showl (nums x) . showString "." .
                   showsPrec n p .  showString " => " . showsPrec n t . showString ")"  
     where nums xs = ["%"++(show n) | n <- [0 .. (length xs - 1)]]
           

toVis map (S x)    = VS(map (toVis map) x)
toVis map (TGen n) = VN("v" ++ (show n))
toVis map (TVar _ _) = VN "?"
 
visKind = toVis mapK
visType = toVis mapT

data Vis s
    = VS (s (Vis s))
    | VN String
 
instance Show (Vis T) where
      show (VN gen)       = gen 
      show (VS tstruct)   = show tstruct

instance Show (Vis K) where
      show (VN gen) = gen
      show (VS tstruct) = show tstruct

instance Show (Kind a) where
  show t = show(visKind t)

 
---------------------------------------------

a:b:c:d:_ = [ TGen i | i <- [0..] ]

simpleEnv =
  [(UnQual "+",Sch[star] [num a] (tArrow a (tArrow a a)))
  ,(UnQual "*",Sch[star] [num a] (tArrow a (tArrow a a)))
  ,(UnQual "-",Sch[star] [num a] (tArrow a (tArrow a a)))
  ,(UnQual ":",Sch[star,star] [] (tArrow a (tArrow (tlist a) (tlist a))))
  ,(UnQual "True",Sch[] [] tBool)
  ,(UnQual "False",Sch[] [] tBool)
  ]


---------------------------------------------------------------
-- a declaration like
--    type T a b = (a,b -> Int)
-- is stored in an environment with type  [(HsName,([HsName],HsType))]
-- e.g.   (T,([a,b],(a,b -> Int))) :: more
-- expandType walks over a type. At every application it tests if that application
-- matches some fully applied instance of (T a b). Suppose it does and looks like
-- (T Int String). Then we build a substitution [(a,Int),(b,String)] and apply
-- it to (a,b -> Int). If it doesn't, we just recursively expand the sub-types.

expandType :: [(HsName,([HsName],HsType))] -> HsType -> Type a
expandType env (x @ (Typ(HsTyApp f a))) = 
    case matchApp env x of
      Nothing -> S(HsTyApp (expandType env f) (expandType env a))
expandType env (Typ x) = S(mapT (expandType env) x)      
 
matchApp :: [(HsName,([HsName],HsType))] -> HsType -> Maybe (Type a)
matchApp env t = walkSpine t []
  where walkSpine (Typ(HsTyApp x y)) ts = walkSpine x (expandType env y : ts)
        walkSpine (Typ(HsTyCon nm)) ts = applySub nm env ts
        walkSpine _ ts = Nothing
        applySub nm env ts = 
           case lookup nm env of
             Nothing -> Nothing
             Just(vs,t) -> if length vs == length ts
                              then Just(rebuild (zip vs ts) t)
                              else Nothing
  
--------------------------------------------------------
class TCEnv env   where
  extTconstr  :: HsName -> GT K Sort (STRef a) -> env a -> env a
  extTySyn    :: HsName -> [HsName] -> Type a  -> env a -> env a
  extTrm      :: HsName -> Scheme a -> env a -> env a
  lookTconstr :: env a -> HsName -> GT K Sort (STRef a)
  lookTySyn   :: env a -> HsName -> ([HsName],Type a)
  lookTrm     :: env a -> HsName -> Scheme a
  lookTconstrOpt    :: env a -> HsName -> Maybe (GT K Sort (STRef a))
  lookTySynOpt      :: env a -> HsName -> Maybe ([HsName],Type a)
  lookTrmOpt        :: env a -> HsName -> Maybe (Scheme a)
  getKindEnv  :: env a -> [(HsName, GT K Sort (STRef a))]
  getTermEnv  :: env a -> [(HsName, Scheme a)]
  env0        :: env a



data TEnv a = E { typeSyns   :: [(HsName, ([HsName], Type a))]
                , termEnv    :: [(HsName, Scheme a)] 
                , kindEnv    :: [(HsName,GT K Sort (STRef a))] }
                           deriving Show



(E a b c) +|+ (E d e f)  = E (a++d) (b++e) (c++f)
instance TCEnv TEnv where
   env0 = E [] [] []  
   extTconstr  n t env     = env { kindEnv = (n,t) : kindEnv env }
   extTySyn    n ns t env  = env { typeSyns = (n, (ns,t)) : typeSyns env }
   extTrm      n sch env   = env { termEnv =  (n,sch)    : termEnv env}
   lookTconstr env  n      = case lookup n (kindEnv env) of  
                                  Just x  -> x
                                  Nothing -> error $ "Not found: "++(show n)
   lookTySyn   env n       = case lookup n (typeSyns env) of
                                  Just x  -> x
                                  Nothing -> error $ "Not found: type synonym " ++ (show n)
   lookTrm     env n       = case lookup n (termEnv env) of 
                                  Just x    -> x
                                  Nothing   -> error $ "Not found: no type for " ++ (show n)
   getKindEnv env         = kindEnv env
   getTermEnv env         = termEnv env
---------------------------------------------------------
