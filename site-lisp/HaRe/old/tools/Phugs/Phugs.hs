module Phugs where


----------------------------------------------------------------------
-- AST, etc.
----------------------------------------------------------------------

import Syntax hiding (E,P,D)
import PrettyPrint(pp)

type Name = String
data Op = Plus | Mult | IntEq | IntLess
data LS = Lazy | Strict deriving Eq

data P --- Nested Patterns
  = Pconst Integer          -- { 5 }
  | Pvar Name               -- { x }
  | Ptuple [P]              -- { (p1,p2) }
  | Pcondata Name [P]       -- data T1 = C1 t1 t2; {C1 p1 p1} = e 
  | Pnewdata Name P         -- newtype T2 = C2 t1;  {C2 p1} = e
  | Ptilde P                -- { ~p }
  | Paspat Name P           -- { x@p }
  | Pwildcard               -- { _ }

data E 
  = Var Name             -- { x }
  | Const Integer        -- { 5 }
  | App E E              -- { f x }
  | Abs [P] E            -- { \ p1 p2 -> e }
  | TupleExp [E]         -- { (e1,e2) }
  | ConApp Name [(E,LS)] -- data T1 = C1 t1 t2 \nl p = {C1 e1 e2}
  | NewApp Name E        -- newtype T2 = C2 t1 t2 \nl p = {C2 e1 e2}
  | Seq E E              -- { seq e1 e2 }               
  | Bin Op E E           -- { e1 + e2 }
  | Cond E E E           -- { if e1 then e2 else e3 }
  | Let [D] E            -- { let x=e1 \nl   y=e2 in e3 }
  | Case E [Match]       -- { case e of m1 \nl m2 }
  | Undefined            -- undefined

type Match = 
      (P, B, [D])        -- case e of { pat -> body where decs } 

data D 
  = Fun Name [Clause]    -- { f p1 p2 = b where decs }
  | Val P B [D]          -- { p = b where decs }

type Clause = 
      ([P],B,[D])        -- f { p1 p2 = body where decs }
data B
  = Guarded [(E,E)]      -- f p { | e1 = e2 | e3 = e4 } where ds
  | Normal E             -- f p = { e } where ds


showB :: B -> String
showB (Normal e) = showE e
showB (Guarded ps) = foldr f "\n" ps
   where f (e1,e2) ans = "| "++(showE e1) ++ " = " ++(showE e2)++ ans

showWhere ds = if null ds then "" else "   where "

showD :: D -> String
showD (Val p body ds) =  "VALDEF " ++ showP p ++ "=" ++ (showB body) ++ "\n" ++
                         (showWhere ds) ++ (showDs ds)
showD (Fun nm xs) = "FUNDEF "++ (foldr (++) "" (map f xs))
   where f (ps,body,ds) = 
           nm ++ " " ++(showPs ps) ++ " = " ++(showB body) ++ "\n" ++
           (showWhere ds) ++ (showDs ds)
   

showDs dcls = foldr (++) "" (map showD dcls)

showOp :: Op -> String
showOp Plus = "+"
showOp Mult = "*"
showOp IntEq = "=="
showOp IntLess = "<"

showP (Pconst i)      = "LitPat("++show i++")"
showP (Pvar n)        = "VarPat(\""++n++"\")"
showP (Pcondata n ns) = "ConstrPat(" ++ n ++ "," ++ (mkSlist ns) ++")"
showP (Paspat n p)    = "AsPattern("++n++","++show p++")"
showP (Pnewdata n x)  = error "no new constructor pattern yet"
showP (Ptilde p)      = error "no tilde pattern yet"
showP (Ptuple ps)     = "TuplePat(" ++ mkSlist ps ++ ")" 
showP Pwildcard       = "WildCard"

showPs [] = ""
showPs (p:ps) = (showP p)++" "++(showPs ps)

{- Pretty prints a haskell list expression into a stratego list -}
mkSlist = foldr 
             (\ s t -> if t/="Nil" then (show s++","++t) else (show s))
             "Nil" 

{- N.b., the resulting string is Stratego code -}
showE :: E -> String
showE (Var nm)     = "HVar(\""++nm++"\")"
showE (Const i)    = "HLit("++show i++")"
showE (App d d')   = "HApp(" ++ showE d ++ "," ++ showE d' ++ ")"
showE (Abs p d)    = "(\\" ++ (foldr (++) " " (map showP p)) ++ " -> " 
                           ++ showE d ++ ")"
showE (TupleExp l) =  "(" ++   
                (foldr (\ s t -> 
                            if t/="" then (showE s) ++ "," ++ t
                                     else (showE s)) 
                       "" l)
                      ++ ")"
showE (ConApp n l) =  "(" ++ n ++ " " ++  
                (foldr (\ (s,ls) t -> 
                            let sa = if (ls == Strict) then "!" else "" 
                            in
                                 if t/="" then sa ++ (showE s) ++ "," ++ t
                                     else sa ++ (showE s)) 
                        "" l)
                      ++ ")"
showE (NewApp n x)  = "(" ++ n ++ " " ++  (showE x) ++ ")"                     
showE (Seq x y)     = "(seq "++(showE x) ++ " " ++ (showE y) ++ ")"
showE (Bin op d d') = "(" ++ showE d ++ " " ++ showOp op ++ " " ++ 
                               showE d' ++ ")"
showE (Cond b e1 e2) = "if "++showE b++" then "++showE e1++" else "++show e2
showE (Let dcls d)   = "let " ++ 
                            foldr (++) "" (map showD dcls)
                              ++ " in " ++ showE d
showE (Case e ms) =
      "(case " ++ showE e ++ " of " ++ 
           (foldr (++) "" 
           (map (\ alt -> "[" ++ (showAlt alt) ++ "]") ms)) ++ ")"
   where showAlt (p,b,ds) = show p ++ " -> " ++ show b ++ "\n" ++ showDs ds


instance Show D where
  show = showD

instance Show E where
  show = showE

instance Show P where
  show = showP

instance Show B where
  show = showB

-----------------------------------------------------------------------

bad x = error "not yet"

--translateP :: HsPat -> P
translateP (Pat p) =
 case mapP translateP p of
   HsPId n -> Pvar (showId n)
   HsPLit (HsInt _ n) -> Pconst n
   HsPInfixApp x op y -> Pcondata (show op) [x,y]
   HsPApp n ps -> Pcondata (show n) ps
   HsPTuple ps -> Ptuple ps
   HsPIrrPat p -> Ptilde p
   HsPParen p -> p
   other -> error ("no "++(show other)++" patterns yet")


--translateD :: HsDecl -> D
translateD (d @ (Dec x)) =
 case mapD translateE translateP (map translateD) bad bad bad x of
   HsPatBind loc p b ds -> Val p (translateRhs b) ds
   HsFunBind loc matches -> Fun (name matches) (map g matches)
      where name ((HsMatch loc nm ps rhs ds): ms) = (showId (HsVar nm))
            g (HsMatch loc nm ps rhs ds) = (ps,translateRhs rhs,ds)
   other -> error ("illegal dec "++(show d))          
      
--translateRhs :: HsRhs E -> B
translateRhs (HsBody e) = Normal e
translateRhs (HsGuard triples) = Guarded(map f triples)
        where f (loc,guard,body) = (guard,body)

--translateAlt :: HsAlt E P [D] -> (P,B,[D])
translateAlt (HsAlt loc pat rhs ds) = (pat,translateRhs rhs,ds)

--translateE :: HsExp -> E
translateE (e @ (Exp x)) = 
 case mapE translateE translateP (map translateD) bad bad x of 
   HsId n                 -> Var (showId n)
   HsApp x y              -> App x y
   HsLit (HsInt _ n)      -> Const n
   HsInfixApp x op z      -> App (App (Var (showId op)) x) z
   HsNegApp _ x           -> App (Var "negate") x  
   HsLambda ps e          -> Abs ps e
   HsLet ds e             -> Let ds e
   HsIf x y z             -> Cond x y z
   HsCase e alts          -> Case e (map translateAlt alts)
   HsTuple xs             -> TupleExp xs
   HsList xs              -> f xs
      where f [] = ConApp "[]" []
            f (x:xs) = ConApp ":" [(x,Lazy),(f xs,Lazy)]
   HsParen x              -> x
   HsLeftSection x op     -> Abs[Pvar "zzz"] (App (App (Var (show op)) x) 
                                             (Var "zzz"))
   HsRightSection op y    -> Abs[Pvar "zzz"] (App (App (Var (show op)) 
                                             (Var "zzz")) y)
   other -> error ("no translation yet for: "++(show e))


--showId (HsVar x) = show x
--showId (HsCon x) = show x

showId x = pp x

----------------------------------------------------------------------
-- Values
----------------------------------------------------------------------

data V 
  = Z Integer        --- scalars
  | FV (V -> V)      --- functions
  | Tagged Name [V]  --- algebraic structured data
  | TV [V]           --- tuple values 

-------------------------------------------------------------
-------------------------------------------------------------
type Env = Name -> V              -- Maps Names to Values V

xEnv :: Env -> [Name] -> [V] -> Env
xEnv rho (x:xs) (b:bs) = (xEnv (tweek rho x b) xs bs)
    where tweek f x y = \ z -> if x == z then y else f z
xEnv rho [] [] = rho

------------------------------------------------------------------
{-
There are variables in a pattern p with the appropriate types corresponding 
to the range of this function x1::b1, ..., xn::bn.

Call these variables the "fringe" of p. (fringe p) returns the free 
variables of p in *order* of occurrence from left to right. -}

-- returns the fringe of p in order  from left to right.
fringe :: P -> [Name]
fringe (Pconst i) = []
fringe (Pvar x) = [x]
fringe (Pcondata n ps) = foldr (++) [] (map fringe ps)
fringe (Ptilde p) = fringe p
fringe (Ptuple ps)= foldr (++) [] (map fringe ps)
fringe (Paspat n p) = n : (fringe p)
fringe Pwildcard = []

data Predicate = Univ | Strong Predicate | List [Predicate] 
               | TCongruence Name [Predicate] deriving Show


patPred :: P -> [(Name,Predicate)] -> Bool -> (Predicate,Bool)
patPred (Pvar x) sigma b   = (purify $ lookup x sigma, is_strong (purify $ lookup x sigma))
                 where     
	                 is_strong (Strong _) = True
	                 is_strong _          = False
                     --xb                   = purify $ lookup x sigma		   
					 
patPred Pwildcard sigma b       = (Univ,False)
patPred (Ptilde p) sigma b      = patPred p sigma False
patPred (Pcondata n ps) sigma b = 
       let (List preds, s) = map_patPred ps sigma b
	   in
	      if (s || b) then 
		         (Strong (TCongruence n preds), True)
		  else   (Univ, False)

map_patPred :: [P] -> [(Name,Predicate)] -> Bool -> (Predicate,Bool)
map_patPred [] sigma b     = (List [], False)
map_patPred (p:ps) sigma b = (List (pp:pps), s1 || s2)
                   where
                       (pp,s1)       = patPred p sigma b
                       (List pps,s2) = map_patPred ps sigma b

pat2pred :: P -> [Predicate] -> Predicate
pat2pred p plist = fst (patPred p (zip (fringe p) plist) True)

frD :: [D] -> [Name]
frD [] = []
frD ((Fun f _):ds) = f : (frD ds)
frD ((Val p _ _):ds) = fringe p ++ (frD ds)

--- This collects the function names & patterns from declarations
--- as a single tuple pattern
declared :: [D] -> P
declared ds = ptuple $ map getbinder ds
     where     
	     getbinder (Fun f _)   = Pvar f
	     getbinder (Val p _ _) = tildefy p

arity (Pvar x) = 1
arity (Ptuple ps) = sum(map arity ps)
arity (Pcondata n ps) = sum(map arity ps)
arity (Ptilde p) = arity p
		 
tuple :: [V] -> V
tuple [v] = v
tuple vs = TV vs

tagtuple :: [V] -> V
tagtuple [v] = v
tagtuple vs = Tagged "tuple" vs

ptuple :: [P] -> P
ptuple [p] = p
ptuple ps = Pcondata "tuple" ps

tildefy :: P -> P
tildefy p = case p of 
                  (Ptilde p') -> p
                  (Pvar x)    -> p
                  _           -> (Ptilde p)

-------------------------------------------
--      Important Semantic Operators     --
-------------------------------------------

-- Composition operators (N.b., both diagrammatic order.)
(>>>) :: (a -> b) -> (b -> c) -> a -> c
f >>> g = g . f              -- Functional

(<>) :: (a -> Maybe b) -> (b -> Maybe c) -> a -> Maybe c
f <> g = \x -> f x >>= g     -- Kleisli 

bottom :: a                             -- domains are pointed
bottom = undefined

purify :: Maybe a -> a                  -- "run" of Maybe monad
purify (Just x) =  x
purify Nothing  = bottom

fix :: (a -> a) -> a                    -- least fixed point
fix f = f (fix f)

semseq :: V -> V -> V
semseq x y = case x of 
                (Z _)        -> y  ;
				(FV _)       -> y  ;
			    (Tagged _ _) -> y  ;
				(TV _)       -> y  

sharp :: Int -> [V] -> (V -> V) -> V    -- Currying
sharp 0 vs beta = beta (tuple vs)
sharp n vs beta = FV $ \ v -> sharp (n-1) (vs++[v]) beta

app :: V -> V -> V                      -- Application
app (FV f) x = f x

fatbar :: (a -> Maybe b) -> (a -> Maybe b) -> (a -> Maybe b)
f `fatbar` g = \ x -> (f x) `fb` (g x)
     where 
          fb :: Maybe a -> Maybe a -> Maybe a
          Nothing `fb` y = y
          (Just v) `fb` y = (Just v)
		  


{- The function match is used to construct the meaning of a Match. -}
match :: Env -> (P, B, [D]) -> V -> Maybe V
match rho (p,b,ds) = mP p <> (\vs -> mwhere (xEnv rho xs vs) b ds)
     where xs = fringe p

-- used in letbind and mE
lam :: P -> E -> Env -> V -> V
lam p e rho = (mP p <> ((\vs -> mE e (xEnv rho xs vs)) >>> Just)) >>> purify
     where xs = fringe p

mcase :: Env -> [Match] -> V -> V
mcase rho ml = (fatbarL $ map (match rho) ml) >>> purify
                     where fatbarL :: [V -> Maybe V] -> V -> Maybe V
                           fatbarL ms = foldr fatbar (\ _ -> (Just bottom)) ms

{-
(letbind rho ds e) is the meaning of Haskell's mutually recursive
let construct. Its definition uses a standard technique for 
defining mutual recursion with explicit fix-points:

let p1 = e1    
      ...
    pn = en    === (\(p1,...,pn) -> e) (fix \(~p1,...,~pn) -> (e1,...,en))
in 
    e

In order for the fixpoint to be defined, each pattern pi in the argument 
to fix is "~"-ed, so that the function is lazy.
-}

letbind ::  Env -> [D] -> E -> V
letbind rho [] e = mE e rho
letbind rho ds e = (lam dp e rho) v
    where
       dp = tildefy $ declared ds
       xs = frD ds
       decls env = tagtuple $ map (\d -> mD d env) ds
       v = fix $ ((mP dp) <> 
                   ((\vs -> decls (xEnv rho xs vs)) >>> Just)) >>> purify

mwhere ::  Env -> B -> [D] -> Maybe V
mwhere rho b [] = mB b rho
mwhere rho b ds = (wherecls dp b rho) v
 where
   wherecls p b rho = (mP p <> (\vs -> mB b (xEnv rho xs vs)))
                         where xs = fringe p
   dp = tildefy $ declared ds
   xs = frD ds
   decls env = tagtuple $ map (\d -> mD d env) ds
   v = fix $ ((mP dp) <> 
               ((\vs -> decls (xEnv rho xs vs)) >>> Just)) >>> purify
			 	   
{-
Translation of function bindings from Haskell98 Report (p. 54):

             x p(1,1) ... p(1,k)  match1
                      ...
             x p(n,1) ... p(n,k)  matchn

 is equivalent to
            x = \x1 ... xn -> case (x1,...,xn) of
			                            (p(1,1),...,p(1,k)) ->  match1
                                            ...
                                        (p(n,1),...,p(n,k)) ->  matchn  
	        where x1,...,xn are fresh variables.
			
The function below, "mD", is constructed similarly, although without any
variable generation. 
-}



--------------------------------------------
---          semantic functions          ---
--------------------------------------------

mE  :: E -> Env -> V
mP  :: P -> V -> Maybe [V]
mB  :: B -> Env -> Maybe V
mD :: D -> Env -> V

phugs ds = mE (Let ds (Var "topLevel")) rho0

--(App (Var "odd") (Const 3))


rho0 = xEnv rhoNull ["==","-","*","True","False"] [eqZ,minusZ,multZ,tt,ff] 
    where rhoNull = \msg -> (error ("You're applying the empty env to:"++msg))
          eqZ = FV $ \ (Z i) -> (FV $ \ (Z j) -> 
                        if i==j then (Tagged "True" [])
                                else (Tagged "False" []))
          minusZ = FV $ \ (Z i) -> (FV $ \ (Z j) -> (Z $ i-j))
          multZ  = FV $ \ (Z i) -> (FV $ \ (Z j) -> (Z $ i*j))
          tt     = Tagged "True" []
          ff     = Tagged "False" []

-----------------------------------------------------------------
-- The meaning of expressions
-----------------------------------------------------------------

ifV :: V -> a -> a -> a
ifV (Tagged "True" []) x y = x
ifV (Tagged "False" []) x y = y



mE (Var n) rho        = rho n
mE (Const i) rho      = (Z i)

mE (TupleExp es) rho  = TV $ map (\e-> mE e rho) es
mE (Cond e0 e1 e2) rho = ifV (mE e0 rho) (mE e1 rho) (mE e2 rho)

mE (App e1 e2) rho    = app (mE e1 rho) (mE e2 rho)
mE (Abs [p] e) rho    = FV $ lam p e rho
mE (Abs ps e) rho     = mE (foldr (\p -> \body -> Abs [p] body) e ps) rho

mE (Let ds e) rho     = letbind rho ds e 
mE (Case e ml) rho    = mcase rho ml (mE e rho)

mE (ConApp n el) rho  = evalL el rho n [] 
   where evalL :: [(E,LS)] -> Env -> Name -> [V] -> V
         evalL [] rho n vs              = Tagged n vs
         evalL ((e,Strict):es) rho n vs = semseq (mE e rho) 
		                                         (evalL es rho n (vs ++ [mE e rho]))
         evalL ((e,Lazy):es) rho n vs   = evalL es rho n (vs ++ [mE e rho])

mE (NewApp n e) rho   = mE e rho

mE Undefined rho      = bottom

mE (Seq e1 e2) rho    = semseq (mE e1 rho) (mE e2 rho)
mE (Bin op e1 e2) rho = binOp op (mE e1 rho) (mE e2 rho)
           where binOp Plus (Z i) (Z j)    = Z $ i+j
                 binOp Mult (Z i) (Z j)    = Z $ i*j
                 binOp IntEq (Z i) (Z j)   = Tagged (equal i j) []
                 binOp IntLess (Z i) (Z j) = Tagged (less i j) []
                 equal i j = if i==j then "True" else "False"
                 less i j  = if i<j then "True" else "False"

mB (Normal e) rho               = Just (mE e rho)
mB (Guarded gl) rho             = ite gl rho
   where ite [] rho         = Nothing   
         ite ((g,e):gs) rho = ifV (mE g rho) (Just (mE e rho)) (ite gs rho)

{- 
A pattern p may be viewed as a function of type ::a -> Maybe (b1,...,bn).
The denotation of a pattern is represented here as a function ::V -> Maybe [V].
-}
mP (Pvar x) v                    = Just [v]
mP (Pconst i) (Z j)              = if i==j then Just [] else Nothing
mP (Ptuple ps) (TV vs)           = stuple (map mP ps) vs
mP (Pcondata n ps) (Tagged t vs) = if n==t then
                                        stuple (map mP ps) vs
                                   else Nothing
mP (Pnewdata n p) v              = mP p v
mP (Ptilde p) v = Just(case mP p v of
                          Nothing -> replicate (arity p) bottom
                          Just z -> z) 
mP Pwildcard v = Just []

stuple :: [V -> Maybe [V]] -> [V] -> Maybe [V]
stuple [] []         = Just []
stuple (q:qs) (v:vs) = do v'  <- q v
                          vs' <- stuple qs vs
                          Just (v'++vs')

mD (Fun f cs) rho  = sharp lps [] body
     where 
       body = mcase rho (map (\(ps,b,ds) -> (ptuple ps, b,ds)) cs)
       lps  = length ((\(pl,_,_)->pl) (head cs))
	                              
mD (Val p b ds) rho = purify $ mwhere rho b ds 

--grunt (Val p b ds) rho 
--grunt (Val p b ds) rho = fix $ match rho (tildefy p,b,ds) >>> purify 


showV :: V -> String
showV (Z i)            = show i
showV (FV _)         = "(function value)"
showV (Tagged n [])    = n
showV (Tagged n [v])   = "("++n++" ?)"
showV (Tagged n [v1,v2])   = "("++n++" "++show v1++" "++show v2++")"
showV (TV [])    = "()"
showV (TV [v])   = "("++show v++")"
showV (TV [v1,v2])    = "("++show v1++","++show v2 ++")"

instance Show V where
  show = showV

{-
rho0 = (\msg -> error "hey - you're applying the empty env!")
go e = mE e rho0
-}
omegafac n = let fac x = if x==0 then 1 else x * (fac (x-1)) in fac n

omega :: V
omega = case (fix (\ i -> i) (Z 9)) of 
                      FV f -> FV f

omega1 :: Integer -> (Integer -> Integer) -> Integer -> Integer
omega1 x f = if x==0 then f else (omega1 (x-1) f)
			
