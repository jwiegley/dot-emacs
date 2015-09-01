module HaskellCoreLite1_2 where 

{-
Differences from HCL1.1:

This version has explicit pattern-matching failure in the type of "match."
I.e., match :: P -> M Value -> M (Maybe EnvFrag)

So, now M now longer has two error types "Fatal" and "Trappable" - they're
all fatal now. Also, fatbar has gone away.

BTW, most/all of the changes are marked with comments starting with "N.b."

-}

type Name = String

data Op = Plus | Mult | IntEq | IntLess

data LS = Lazy | Strict deriving Eq

data E
  = Var Name
  | App E E
  | Abs P E
  | Let [D] E
  | Case E [Match]
  | PairExp E E
  | TupleExp [E]
  | Const Integer
---  | ConApp Name [E] 
  | ConApp Name [(E,LS)]
  | NewApp Name E
  | Boom
  | Undefined
--- Above is the "core", below various extras
  | Bin Op E E
  | Cond E E E
  | Tconst 
  | Fconst

data Match = Guarded P [(E,E)] [D]
           | Normal P E [D]

--- N.b., these are nested patterns.
data P = Pconst Integer
       | Pvar Name
       | Ppair P P
       | Ptuple [P]
       | Pcondata Name [P]  
       | Pnewdata Name P
       | Ptilde P

type D = (P,E)

showD :: D -> String
showD (p,le) =  " " ++ showP p ++ "=" ++ (showE le) ++ " " 

showDecls dcls = foldr (++) "" (map (\(p,e)-> showD (p,e)) dcls)


showOp :: Op -> String
showOp Plus = "+"
showOp Mult = "*"
showOp IntEq = "=="
showOp IntLess = "<"

showP (Pconst i) = show i
showP (Pvar n) = n
showP (Pcondata n ns) = 
                "(" ++ n ++ " " ++ 
                (foldr (\ s t -> if t/="" then (showP s) ++ "," ++ t
                                     else (showP s)) 
                        "" ns)
                ++ ")"
showP (Pnewdata n x) = "(" ++ n ++ " " ++ (showP x) ++ ")"              
showP (Ptilde p) = "~" ++ (showP p)

showM :: Match -> String
showM (Normal p e ds) = showP p ++ "->" 
                                ++ showE e 
                                ++ " where " ++ showDecls ds
showM (Guarded p glist ds) = 
    (foldr (++) "" 
       (map (\(g,b) -> showP p ++ " | " ++ showE g ++ "->" ++ showE b) glist))
                    ++ " where " ++ showDecls ds

showE :: E -> String
showE (Const i) = show i
showE Tconst = "True"
showE Fconst = "False"
showE (Var nm) = nm
showE (Abs p d) = "(\\" ++ (showP p) ++ " -> " ++ showE d ++ ")"
showE (App d d') = "(" ++ showE d ++ " " ++ showE d' ++ ")"
showE (Let dcls d) = "let " ++ 
                          foldr (++) "" (map (\(p,e)-> showD (p,e)) dcls)
                            ++ 
                        " in " ++ showE d
showE (ConApp n l) =  "(" ++ n ++ " " ++  
                (foldr (\ (s,ls) t -> 
			    let sa = if (ls == Strict) then "!" else "" 
			    in
				 if t/="" then sa ++ (showE s) ++ "," ++ t
                                     else sa ++ (showE s)) 
                        "" l)
                      ++ ")"
showE (NewApp n x) = "(" ++ n ++ " " ++  (showE x) ++ ")"                     

showE (PairExp n l) = "<"++showE n++","++ showE l ++ ">"
showE (Bin op d d') = "(" ++ showE d ++ " " ++ showOp op ++ " " ++ 
                               showE d' ++ ")"
showE Tconst = "true"
showE Fconst = "false"
showE (Case e ms) =
      "(case " ++ showE e ++ " of " ++ 
           (foldr (++) "" (map (\m -> "[" ++ (showM m) ++ "]") ms)) ++ ")"


instance Show E where
  show = showE

----------------------------------------------------------------------
-- Values
----------------------------------------------------------------------

type EnvFrag = [(Name,M Value)]

data Value
  = 
--- scalars
    Z Integer
  | BV Bool
--- CBN functions
  | Fun (M Value -> M Value)
--- Generic structured data
  | Tagged Name [M Value]
--- values for all tuples:
  | TupleVal [M Value]

data Fix a = Fix (Fix a -> a)
fix = \ f -> (\ (Fix x) -> 
                   (f (\ a -> x (Fix x) a)))
                      (Fix (\ (Fix x) -> (f (\ a -> x (Fix x) a))))

showValue :: Value -> String
showValue (Z i) = show i
showValue (BV i) = show i
showValue (Fun _) = "(function)"
showValue (Tagged n arglist) = "(" ++ n ++ " " ++ (present (map splat arglist)) ++ ")"

present (x:(y:rest)) = (show x)++" "++(present (y:rest))
present (x:[]) = show x
present [] = ""

instance Show Value where
  show = showValue

splat phi = (deM phi (\msg -> error "hey - you're applying the empty env!"))
run le = (deM (eval le) (\msg -> error "hey - you're applying the empty env!"))

----------------------------------------------------------------------
-- Errors
----------------------------------------------------------------------

data Error a = Ok a | Err String

----------------------------------------------------------------------
-- Error monad
----------------------------------------------------------------------


errUnit :: a -> Error a
errUnit = Ok


errBind :: Error a -> (a -> Error b) -> Error b
errBind x f = case x of
                     (Ok v) -> f v
                     (Err msg) -> (Err msg)

instance Monad Error where
  return = errUnit
  (>>=) = errBind

showEC x =
       case x of
            (Ok v) -> show v
            (Err msg) -> show msg

showError :: Show a => Error a -> String
showError x =
       case x of
            (Ok v) -> show v
            (Err msg) -> show msg

instance Show a => Show (Error a) where
    show = showError

raise0 = Err

----------------------------------------------------------------------
-- Environments
----------------------------------------------------------------------

type Env = Name -> M Value

----------------------------------------------------------------------
-- M = Environment+Error 
----------------------------------------------------------------------

newtype M a = M (Env -> (Error a))

mUnit :: a -> M a
mUnit a = M (\rho -> return a)


mBind :: M a -> (a -> M b) -> M b
mBind x f =
        M (\rho -> 
                 do { v <- (deM x) rho ; deM (f v) rho })

instance Monad M where
  return = mUnit
  (>>=) = mBind

deM (M x) = x

lift :: Error a -> M a
lift ec = M (\ _ ->  ec)

----------------------------------------------------------------------
-- Non-standard Morphisms
----------------------------------------------------------------------

raise :: String -> M a
raise = \msg -> lift (raise0 msg)

rdEnv :: M Env
rdEnv = M (\rho -> return rho)

tweek f x y = \ z -> if x == z then y else f z

xEnv :: Env -> Name -> M Value -> Env
xEnv rho n phi = tweek rho n phi

inEnv :: Env -> M a -> M a
inEnv rho (M x) = M (\ _ -> x rho)

----------------------------------------------------------------------
-- 
----------------------------------------------------------------------

--- these functions/PairVal should be replaced with select/Tagged:

proj :: Int -> M Value -> M Value
proj n phi = do { (TupleVal mvals) <- phi ; mvals !! (n-1)  }

--- N.b., checkTag now strips off the tag "t"
checkTag :: Name -> M Value -> M Value
checkTag tag arg =
         do { (Tagged t mvals) <- arg
            ; if t==tag then return (TupleVal mvals)
              else raise $ "Tag " ++ t ++ "!="++tag
              }


concatM ::Monad m => [m [a]] -> m [a]
concatM x = sequence x >>= (return . concat)

---
--- N.b., the meaning of match has changed so that
--- pattern failure is explicit in the range here:
---
match :: P -> M Value -> M (Maybe EnvFrag)
match (Pvar x) arg = return $ Just [(x,arg)]
match (Ptilde p) arg = return $ Just (lazymatch p arg)
match (Pconst i) arg = do { (Z v) <- arg
                          ; if v==i then 
                                    return $ Just []
                            else return Nothing
                            }
match (Ppair p1 p2) arg = 
      do { (TupleVal mvals) <- arg
         ; vbl1 <- match p1 (head mvals)
         ; vbl2 <- match p2 (head $ tail mvals)
         ; case (vbl1,vbl2) of
             (Just vl1, Just vl2) ->return $ Just (vl1 ++ vl2) 
             _ -> return Nothing
         }
match (Ptuple ps) arg = 
   do { (TupleVal mvals) <- arg
      ; sequence (map (\(p,phi) -> match p phi) (zip ps mvals)) 
                 >>= (return . concatM)
             }
match (Pcondata tag ps) arg = 
   do { (Tagged t mvals) <- arg
      ; if tag==t 
        then
           sequence (map (\(p,phi) -> match p phi) (zip ps mvals)) 
                >>= (return . concatM)
        else return Nothing
             }
match (Pnewdata n p) arg = match p arg
  


lazymatch :: P -> M Value -> EnvFrag
lazymatch (Pconst k) mv = []
lazymatch (Pvar x) mv = [(x,mv)]
lazymatch (Ptilde p) mv = lazymatch p mv
lazymatch (Ppair p1 p2) mv = 
          lazymatch p1 (proj 1 mv) ++ lazymatch p2 (proj 2 mv)
lazymatch (Pcondata n ps) mv = 
   concat (map (\(i,p) -> lazymatch p (proj i (checkTag n mv)))
                    (zip [1..(length ps)] ps))
lazymatch (Pnewdata n p) mv = lazymatch p mv                    
lazymatch (Ptuple ps) mvals = 
   concat (map (\(i,p) -> lazymatch p (proj i mvals))
                    (zip [1..(length ps)] ps))


app :: M Value -> M Value -> M Value
app x y = do { rho <- rdEnv ; (Fun f1) <- x ; f1 (inEnv rho y) }

addBindings :: Env -> EnvFrag -> Env
addBindings rho [] = rho
addBindings rho ((n,mv):bindings) = addBindings (xEnv rho n mv) bindings

---
--- N.b. ,I use this in the definition of (eval (Let ...)) and in the 
--- meaning of matches as well 
---
letbind :: [(P,E)] -> M a -> M a
letbind pelist phi =
     do { rho <- rdEnv
        ; let rho' = 
               fix (\ r -> 
                 addBindings rho $
                   foldr (++) []  
                         (map (\(p,e)->lazymatch p (inEnv r (eval e))) pelist))
          in
               inEnv rho' phi
               }


eval :: E -> M Value
eval (Const i) = return (Z i)
eval Tconst = return $ BV True
eval Fconst = return $ BV False
eval Boom = eval Boom
eval Undefined = raise "Undefined"
eval (Var n) = do { rho <- rdEnv ; rho n }
---
--- N.b., the abstraction must check if it gets an EnvFrag back.
---
eval (Abs p l) = 
     do { rho <- rdEnv 
        ; return (Fun $ \ arg ->
                   do { vbl <- match p arg 
                      ; case vbl of
                           (Just vl) -> 
                              inEnv (addBindings rho vl) (eval l) 
                           Nothing -> raise "Match Error in Abs"
                           } ) }
eval (App l1 l2) =
     do { rho <- rdEnv
        ; (Fun f1) <- eval l1
        ; f1 (inEnv rho $ eval l2) }
eval (PairExp l1 l2) = 
     do { rho <- rdEnv
        ; return (TupleVal [inEnv rho (eval l1), inEnv rho (eval l2)])
          }
eval (TupleExp es) = 
  do { rho <- rdEnv ; return (TupleVal $ map (\e -> inEnv rho $ eval e) es) }
{-
 This is a little difficult to understand as is, although what is going on is
 quite simple. Here's how I would write it in standard mathematical notation:

[[ c e1 !e2 ]] =
     rdEnv >>= \rho ->
     [[ e2 ]] >>= \ v2 ->
        return (c* (inEnv rho [[e1]]) (return v2))

That is, e2 (annotated as strict) is evaluated early and a trivial computation
"(return v2)" is kept for it. 
-}
eval (ConApp n es) = 
  do { rho <- rdEnv
     ; let evald_es = map (\(e,ls) -> 
			   case ls of
			     Lazy -> return(inEnv rho $ eval e)
			     Strict -> eval e >>= \v -> return(return v)) es
       in
          f evald_es >>= \result -> return (Tagged n $ result)
       }
   where 
	 f [] = return []
	 f (phi:phis) = phi >>= \v-> (f phis) >>= \vs -> return (v:vs)
eval (NewApp n x) = eval x

{-
         (foldr (\ phi phis -> phi >>= \v-> (f phis) >>= \vs -> return (v:vs)) 
                (return [])
foldr (\ phi phis -> phi >>= \v-> (f phis) >>= \vs -> return (v:vs)) 
      (return [])
      es
-}

---
--- N.b., this is the new definition of case.
---
eval (Case e ms) = evalMatchList (map evalM ms) (eval e)
eval (Let pelist le) = letbind pelist $ eval le
eval (Bin op l1 l2) =
     case op of 
      Plus -> 
        do { (Z i1) <- eval l1 
           ; (Z i2) <- eval l2 
           ; return (Z (i1+i2)) }
      Mult -> 
        do { (Z i1) <- eval l1 
           ; (Z i2) <- eval l2 
           ; return (Z (i1*i2)) }
      IntEq ->
        do { (Z i1) <- eval l1 
           ; (Z i2) <- eval l2 
           ; return (BV (i1==i2)) }
      IntLess ->
        do { (Z i1) <- eval l1 
           ; (Z i2) <- eval l2 
           ; return (BV (i1<i2)) }

eval (Cond l1 l2 l3) =
     do { (BV b) <- eval l1
        ; if b then (eval l2) else (eval l3) }

-------------------------------------------------------------
-------------- Matches and their meaning  -------------------
-------------------------------------------------------------

justify :: M Value -> M (Maybe Value)
justify x = x >>= (return . Just)

evalM :: Match -> M Value -> M(Maybe Value)
evalM (Normal p e ds) arg = 
   do { mfrag <- match p arg
      ; case mfrag of
         Nothing -> return Nothing
         Just frag -> do { env <- rdEnv
                         ; inEnv (addBindings env frag) 
                                    $ letbind ds (justify (eval e))
                         }
      }
evalM (Guarded p guards ds) arg =
   do { env <- rdEnv
      ; mfrag <- match p arg
      ; case mfrag of
         Nothing   -> return Nothing
         Just frag -> inEnv (addBindings env frag) 
                               $ letbind ds (evalGuardedList guards)
      }
    where
        evalGuardedList :: [(E,E)] -> M (Maybe Value)
        evalGuardedList [] = return Nothing
        evalGuardedList ((g,b):gs) =
                           do { v <- eval g
                              ; case v of
                                   (BV True)  -> (eval b) >>= (return . Just)
                                   (BV False) -> evalGuardedList gs
                              }

evalMatchList :: [M Value -> M(Maybe Value)] -> (M Value -> M Value)
evalMatchList [] arg = raise "Match Failure"
evalMatchList (f:fs) arg = 
  do { mv <- f arg
     ; case mv of
         Nothing -> evalMatchList fs arg
         Just v -> return v
     }

--------------------------------------------------------------
--------------------------------------------------------------
--------------------------------------------------------------
