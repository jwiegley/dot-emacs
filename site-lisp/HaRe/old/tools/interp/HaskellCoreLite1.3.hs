module HaskellCoreLite1_3 where 

import AST
import Monad

------------------------------------
-- Monadic control structures
------------------------------------

caseM test fail successf =
  do { vbl <- test
     ; case vbl of
         Nothing -> fail
         Just x -> successf x
     }

ifV test thenM elseM =
  do { BV b <- test
     ; if b then thenM else elseM
     }
     
----------------------------------------------------------------------
--- these functions do matching or selection
----------------------------------------------------------------------

proj :: Int -> M Value -> M Value
proj n phi = do { (TupleVal mvals) <- phi ; mvals !! (n-1)  }

checkTag :: Name -> M Value -> M Value
checkTag tag arg =
    do { (Tagged t mvals) <- arg
       ; if t==tag 
            then return (TupleVal mvals)
            else raise("Tag " ++ t ++ "!="++tag)
       }


concatM ::Monad m => [m [a]] -> m [a]
concatM x = sequence x >>= (return . concat)

match :: P -> M Value -> M (Maybe EnvFrag)
match (Pvar x) arg = return (Just [(x,arg)])
match (Ptilde p) arg = return (Just (lazymatch p arg))
match (Pconst i) arg = 
    do { (Z v) <- arg
       ; if v==i 
            then return(Just [])
            else return Nothing
       }
match (Ptuple ps) arg = 
    do { (TupleVal mvals) <- arg
       ; frags <- sequence(zipWith match ps mvals)
       ; return(concatM frags)
       }
match (Pcondata tag ps) arg = 
    do { (Tagged t mvals) <- arg
       ; if tag==t 
         then sequence (zipWith match ps mvals) >>= (return . concatM)
         else return Nothing
       }
match (Pnewdata n p) arg = match p arg
  


lazymatch :: P -> M Value -> EnvFrag
lazymatch (Pconst k) mv = []
lazymatch (Pvar x) mv = [(x,mv)]
lazymatch (Ptilde p) mv = lazymatch p mv
lazymatch (Pcondata n ps) mv = concat(zipWith tagN [1..] ps)
    where tagN i p = lazymatch p (proj i (checkTag n mv))
lazymatch (Pnewdata n p) mv = lazymatch p mv                    
lazymatch (Ptuple ps) mvals = concat(zipWith select [1..] ps)
    where select i p = lazymatch p (proj i mvals)

app :: M Value -> M Value -> M Value
app x y = do { rho <- rdEnv ; (FV f1) <- x ; f1 (inEnv rho y) }

addBindings :: Env -> EnvFrag -> Env
addBindings rho [] = rho
addBindings rho ((n,mv):bindings) = addBindings (xEnv rho n mv) bindings

----------------------------------------------------------
letbind :: [D] -> M a -> M a
letbind ds phi =
     do { rho <- rdEnv
        ; let rho' = fix (\ r -> addBindings rho (addDs ds r))
          in inEnv rho' phi
        }
               
addDs :: [D] -> Env -> EnvFrag
addDs [] r = []
addDs (d:ds) r =
  case d of
   (Val p body ds) -> lazymatch p (inEnv r (letbind ds (evalB body))) ++ (addDs ds r)
   (Fun nm cls) -> (nm,evalCls cls) : (addDs ds r)
    where evalCls :: [([P],B,[D])] -> M Value
          evalCls [] = raise "no guard matches"
          evalCls ((ps,body,ds):cls) = 
              arrow ps (inEnv r (letbind ds (evalB body)))   

arrow :: [P] -> M Value -> M Value
arrow [] b = b
arrow (p:ps) b =
   do { rho <- rdEnv
      ; let f v = caseM (match p v) 
                       (raise "match Error in Fun")
                       (\ vl -> inEnv (addBindings rho vl) (arrow ps b))
      ; return(FV f)
      }

evalB :: B -> M(Value)
evalB (Normal e) = (eval e)
evalB (Guarded []) = error "no guard matches"
evalB (Guarded ((g,e):gs)) = ifV (eval g) (eval e) (evalB (Guarded gs))
      

eval :: E -> M Value
eval (Const i) = return (Z i)
eval Tconst = return (BV True)
eval Fconst = return (BV False)
eval Boom = eval Boom
eval Undefined = raise "Undefined"
eval (Var n) = do { rho <- rdEnv ; rho n }
eval (Abs ps l) = arrow ps (eval l)
eval (App l1 l2) =
   do { rho <- rdEnv
      ; (FV f1) <- eval l1
      ; f1 (inEnv rho $ eval l2) }
eval (TupleExp es) = 
   do { rho <- rdEnv ; return (TupleVal $ map (\e -> inEnv rho $ eval e) es) }
eval (ConApp n es) = 
   do { rho <- rdEnv
      ; let f (e,Lazy) es   = do { cs <- es
                                 ; return ((inEnv rho (eval e)):cs) }
            f (e,Strict) es = do { c <- eval e; cs <- es
                                 ; return((return c):cs)}
      ; cs <- foldr f (return []) es
      ; return(Tagged n cs)
      }  
eval (NewApp n x) = eval x
eval (Case e ms) = evalMatchList (map evalM ms) (eval e)
eval (Let pelist le) = letbind pelist (eval le)
eval (Bin op l1 l2) =
   do { (Z i1) <- eval l1
      ; (Z i2) <- eval l2
      ; return(f op i1 i2)
      }
 where f Plus x y = Z(x + y)
       f Mult x y = Z(x * y)
       f IntEq x y = BV(x==y)
       f IntLess x y = BV(x < y)
eval (Cond l1 l2 l3) = ifV (eval l1) (eval l2) (eval l3)
     

-------------------------------------------------------------
-------------- Matches and their meaning  -------------------
-------------------------------------------------------------

justify :: M Value -> M (Maybe Value)
justify x = x >>= (return . Just)

--- Probably need a new name for this:
evalM :: (P,B,[D]) -> M Value -> M(Maybe Value)
evalM (p,(Normal e),ds) arg = 
   caseM (match p arg) (return Nothing)
         (\frag ->  do { rho <- rdEnv
                       ; inEnv (addBindings rho frag) 
                               $ letbind ds (justify (eval e))
                       })
evalM (p,(Guarded guards),ds) arg =
   caseM (match p arg) (return Nothing) 
      (\frag ->  do { rho <- rdEnv
                    ; inEnv (addBindings rho frag) 
                           $ letbind ds (evalGuardedList guards) } )
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
evalMatchList (f:fs) arg = caseM (f arg) (evalMatchList fs arg) return

--------------------------------------------------------------
--------------------------------------------------------------
--------------------------------------------------------------

splat phi = (deM phi (\msg -> error "hey - you're applying the empty env!"))
run le = (deM (eval le) (\msg -> error "hey - you're applying the empty env!"))
