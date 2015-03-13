module HaskellCoreLite1_1 where 

{-
Differences from 1.0:

1. has irrefutable patterns (done)
2. added explicit fixpoints (done)
3. guards in cases (done)
4. fixing match failure. (done) Added two types of errors - trappable & fatal.
   Now, fatbar distinguishes them.
5. tuples. I'm assuming for the moment that these will
   be implemented as special cases of ADTs. They'll be constructor
   apps of "3tuple", "4tuple", etc. (done)
6. Should also have constructor patterns with arity greater than 1. (done)
-}

type Name = String

data Op = Plus | Mult | IntEq | IntLess

data E
  = Var Name
  | App E E
  | Abs P E
  | Let [D] E
  | Case E [(P,E)]
  | PairExp E E
  | TupleExp [E]
  | Const Integer
  | ConApp Name [E]
  | Boom
  | Undefined
--- Above is the "core", below various extras
  | Bin Op E E
  | Cond E E E
  | Tconst 
  | Fconst
  | Guarded [(E,E)]
  | Match [(E,E)] [D] --- this is the body of a general case statement
                      --- each (E,E) is an guarded expression g-->e 
		      --- where b:BoolExp, and [D] are declarations
		      --- introduced by "where".


--- N.b., these are nested patterns.
data P = Pconst Integer
       | Pvar Name
       | Ppair P P
       | Ptuple [P]
       | Pstrdata Name [P]  
       | Pirref P

type D = (P,E)

showD :: D -> String
showD (p,le) =  " " ++ showP p ++ "=" ++ (showE le) ++ " " 

showOp :: Op -> String
showOp Plus = "+"
showOp Mult = "*"
showOp IntEq = "=="
showOp IntLess = "<"

showP (Pconst i) = show i
showP (Pvar n) = n
showP (Pstrdata n ns) = 
		"(" ++ n ++ " " ++ 
		(foldr (\ s t -> if t/="" then (showP s) ++ "," ++ t
		                     else (showP s)) 
			"" ns)
		++ ")"
showP (Pirref p) = "~" ++ (showP p)

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
		(foldr (\ s t -> if t/="" then (showE s) ++ "," ++ t
		                     else (showE s)) 
			"" l)
		      ++ ")"

showE (PairExp n l) = "<"++showE n++","++ showE l ++ ">"
showE (Bin op d d') = "(" ++ showE d ++ " " ++ showOp op ++ " " ++ 
                               showE d' ++ ")"
showE Tconst = "true"
showE Fconst = "false"
showE (Case e pelist) =
      "(case " ++ showE e ++ " of " ++ 
           (foldr (++) "" (map (\(p,e)-> 
			 "[" ++ (showP p) ++ "--->" ++ (showE e) ++ "]")
			 pelist)) ++ ")"
showE (Match glist dcls) = "{" ++ 
			foldr (++) "" (map (\(g,e)-> showE g ++ "-->" ++ showE
			e) glist)
			    ++ 
                        " where " ++ 
			foldr (++) "" (map (\(p,e)-> showD (p,e)) dcls)
			++ "}"

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
--- Variable Bindings 
  | VarBind EnvFrag
---
---  | PairVal (M Value) (M Value)
--- values for all tuples:
  | TupleVal [M Value]

---Do I need to use something like this?
data Fix a = Fix (Fix a -> a)
fix = \ f -> (\ (Fix x) -> 
		   (f (\ a -> x (Fix x) a)))
		      (Fix (\ (Fix x) -> (f (\ a -> x (Fix x) a))))

showValue :: Value -> String
showValue (Z i) = show i
showValue (BV i) = show i
showValue (Fun _) = "(function)"

instance Show Value where
  show = showValue


----------------------------------------------------------------------
-- Errors
----------------------------------------------------------------------

data ErrorTypes = Trappable String | Fatal String

instance Show(ErrorTypes) where
   show = \ e -> case e of
		      Trappable x -> "Trappable: " ++ x
		      Fatal x -> "Fatal: " ++ x

data Error a = Ok a | ErrorC ErrorTypes

----------------------------------------------------------------------
-- Error monad
----------------------------------------------------------------------


errUnit :: a -> Error a
errUnit = Ok


errBind :: Error a -> (a -> Error b) -> Error b
errBind x f = case x of
		     (Ok v) -> f v
		     (ErrorC msg) -> (ErrorC msg)

instance Monad Error where
  return = errUnit
  (>>=) = errBind

showEC x =
       case x of
	    (Ok v) -> show v
	    (ErrorC msg) -> show msg

showError :: Show a => Error a -> String
showError x =
       case x of
	    (Ok v) -> show v
	    (ErrorC msg) -> show msg

instance Show a => Show (Error a) where
    show = showError

raise0 :: ErrorTypes -> Error a
raise0 = ErrorC

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

raise :: ErrorTypes -> M a
raise = \msg -> lift (raise0 msg)

rdEnv :: M Env
rdEnv = M (\rho -> return rho)

tweek f x y = \ z -> if x == z then y else f z

xEnv :: Env -> Name -> M Value -> Env
xEnv rho n phi = tweek rho n phi

inEnv :: Env -> M a -> M a
inEnv rho (M x) = M (\ _ -> x rho)

--- this isn't the suavest way of defining this
infixr 7 `fatbar`
fatbar a b = M (\rho ->
 --- N.b., no additional evaluation done here
                  case (deM a) rho of
		       (Ok x) -> return x
		       (ErrorC x) -> 
			       case x of 
				    Fatal msg -> ErrorC x
				    Trappable msg -> (deM b) rho
			    )


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
	      else raise $ (Trappable $ "Tag " ++ t ++ "!="++tag)
	      }


--- This is necessary to get the bindings for lambda 
--- abstraction and case. Oddly, lambda abstractions are *not*
--- generally lazy. They're not strict, either, but a
--- hybrid between the two.
--- 
match :: P -> M Value -> M EnvFrag
match (Pvar x) arg = return [(x,arg)]
match (Pconst i) arg = do { (Z v) <- arg
			  ; if v==i then 
				    return []
			    else raise (Trappable "Constant pattern failed")
			    }
match (Ppair p1 p2) arg = do { (TupleVal mvals) <- arg
			     ; vbl1 <- match p1 (head mvals)
			     ; vbl2 <- match p2 (head $ tail mvals)
			     ;    return (vbl1 ++ vbl2) 
				    }
match (Ptuple ps) arg = 
   do { (TupleVal mvals) <- arg
      ; sequence (map (\(p,phi) -> match p phi) (zip ps mvals)) 
		 >>= (return . concat)
	     }
match (Pstrdata tag ps) arg = 
   do { (Tagged t mvals) <- arg
      ; if tag==t 
	then
	   sequence (map (\(p,phi) -> match p phi) (zip ps mvals)) 
		>>= (return . concat)
        else raise (Trappable "Constructor pattern failed")
	     }
match (Pirref p) arg = return (lazymatch p arg)

--- N.b., the range is *not* a computational type because
--- no matching occurs, and so no failure is possible at this
--- point.
---
lazymatch :: P -> M Value -> EnvFrag
lazymatch (Pconst k) mv = []
lazymatch (Pvar x) mv = [(x,mv)]
lazymatch (Ppair p1 p2) mv = 
    (lazymatch p1 (proj 1 mv)) ++ (lazymatch p2 (proj 2 mv))
lazymatch (Pirref p) mv = lazymatch p mv
lazymatch (Pstrdata n ps) mvals = 
         concat
	       (map (\(i,p) -> lazymatch p (proj i (checkTag n mvals))) 
			            (zip [1..(length ps)] ps))
lazymatch (Ptuple ps) mvals = 
         concat
	       (map (\(i,p) -> lazymatch p (proj i mvals))
			            (zip [1..(length ps)] ps))

app :: M Value -> M Value -> M Value
app x y = do { rho <- rdEnv ; (Fun f1) <- x ; f1 (inEnv rho y) }

addBindings :: Env -> EnvFrag -> Env
addBindings rho [] = rho
addBindings rho ((n,mv):bindings) = addBindings (xEnv rho n mv) bindings

eval :: E -> M Value
eval (Const i) = return (Z i)
eval Tconst = return $ BV True
eval Fconst = return $ BV False
eval Boom = eval Boom
eval Undefined = raise (Fatal "Undefined")
eval (Var n) = do { rho <- rdEnv ; rho n }
eval (Abs p l) = 
     do { rho <- rdEnv 
	; return (Fun $ \ arg ->
			   do { vbl <- match p arg 
			      ; inEnv (addBindings rho vbl) (eval l) } ) }
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
eval (ConApp n es) = 
  do { rho <- rdEnv ; return (Tagged n $ map (\e -> inEnv rho $ eval e) es) }
---
--- N.b., eval (Case expr (p,e)) = eval (App (Abs (p,e)) expr)
---
eval (Case e pelist) = 
     foldr fatbar
	   (raise (Fatal "Match Error"))
	   (map (\ (p',e') -> app (eval (Abs p' e')) (eval e)) pelist) 
{-
The above is equivalent to:
     app (eval \p1.e1) (eval e) FATBAR
	       ...
     app (eval \pn.en) (eval e) FATBAR
     raise "Match Failure"
-}	   
---
--- Here, the meaning of a pattern is given by "lazymatch", rather
--- than by "match". This yields real lazy pattern-matching.
---
eval (Let pelist le) = 
     do { rho <- rdEnv
	; let rho' = 
	       fix (\ r -> 
		 addBindings rho $
		   foldr (++) []  
		         (map (\(p,e)->lazymatch p (inEnv r (eval e))) pelist))
	  in
	       inEnv rho' (eval le)
	       }
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
eval (Guarded glist) = 
     foldr fatbar
	   (raise (Fatal "Match Error"))
	   (map (\ (g,e) ->  do { BV b <- eval g
				; if b then 
				       eval e 
				  else raise (Trappable "Guard Failure")
				  })
	        glist)
--- I'm making a point here that "<glist> where <decls>" is equivalent
--- to "let <decls> in <glist>."
eval (Match glist decls) = eval (Let decls (Guarded glist))

--------------------------------------------------------------------
--- Haskell Weirdness.
--------------------------------------------------------------------

data RedBlack a = Red a | Black a
data OneTwo a b = One a | Two a b
instance Show a => Show (RedBlack a) where
    show = \ x -> case x of 
		       Red v -> show v
		       Black v -> show v

omega :: Int -> (Int,Int)
omega = \x -> if True then (omega x) else (omega x)

h0 = (\ (Red x) -> 1) (Black 99)
h1 = (\ (Red (Black x)) -> 1) (Red undefined)
h2 = (\ (Red (Two x (Black y))) -> 1) (Red (Two 1 (Black 9)))
h3 = (\ (Red (Two x (Black y))) -> 1) (Red (Two undefined (Black undefined)))
h4 :: Int
h4 = (\ (Red (Two x (Black y))) -> x) (Red (Two undefined (Black undefined)))

ex1 = case undefined of 1 -> 99        ---> undefined
ex2 = case undefined of x -> 99        ---> 99
ex3 = case undefined of (x,y) -> 99    ---> undefined
ex4 = case undefined of (Red x) -> 99  ---> undefined



-----------------------------------------------------------
--			some examples
-----------------------------------------------------------

redpat = \ x -> Pstrdata "red" [(Pvar x)]
greenpat = \ x -> Pstrdata "green" [(Pvar x)]
blackpat = \ x -> Pstrdata "black" [(Pvar x)]
blackexp = \t -> ConApp "black" [t]
redexp = \t -> ConApp "red" [t]
greenexp = \t -> ConApp "green" [t]
pairpat = Ppair (Pvar "x") (Pvar "y")
black = \ x -> ConApp "black" [x]
red = \ x -> ConApp "red" [x]
green = \ x -> ConApp "green" [x]

run le = showEC (deM (eval le) error)

--- Important to note that abstraction is neither lazy nor strict
--- 
e1 = App (Abs (redpat "x") (Const 1)) (blackexp (Const 19)) ---> error
e2 = App (Abs (redpat "x") (Var "x")) (blackexp (Const 19)) ---> error
e3 = App (Abs (redpat "x") (Var "x")) (redexp (Const 19))   ---> 19
e4 = App (Abs pairpat (Const 4)) (PairExp Boom Boom)        ---> 4
e5 = App (Abs (redpat "x") (Var "x")) Boom                  ---> non-term
e6 = App (Abs (redpat "x") (Var "x")) (ConApp "red" [Boom]) ---> non-term
e7 = App (Abs (redpat "x") (Const 1)) (ConApp "red" [Boom]) ---> 1
e8 = App (Abs pairpat (Var "x")) (PairExp (Const 1) Boom)   ---> 1

c1 = Case Undefined [(Pvar "x", Const 1)]               ---> 1
c2 = Case Undefined [(Pconst 99, Const 1)]              ---> Undefined
c3 = Case Undefined [(redpat "x", Const 1)]             ---> Undefined
c4 = Case (black Undefined) [(redpat "x", Const 1)]     ---> match failure
c5 = Case (red Undefined) [(redpat "x", Const 1)]       ---> 1

c6body = (Case (Var "val") 
			[(redpat "x",    
			  (Case (Var "x") [(blackpat "z",(Const 99))])
				 ),
			 (Pstrdata "red" [greenpat "y"], Const 87)])

c6 = Let [(Pvar "val", redexp (greenexp (Const 1)))] c6body


l1 = Let [(Pconst 1, Const 0)] (Const 99)                 ---> 99
l2 = Let [(redpat "x", Undefined)] (Const 99)             ---> 99
l3 = Let [(redpat "x", black Undefined)] (Const 99)       ---> 99
l4 = Let [(redpat "x", black Undefined)] (Var "x")        ---> red != black
l5 = Let [(redpat "x", red (Const 99))] (Var "x")         ---> 99
l6 = Let [(redpat "x", black Undefined),
	  (redpat "y", green (Const 99))] (Var "x")       ---> red != black


{-
HaskellCoreLite> let (Red x) = Black 19 in 87
87
HaskellCoreLite> let (Red x) = Black 19 in x

Program error: {v1405 (RedBlack_Black (Num_fromInt instNum_v35 19))}
-}

{- 
   BTW, this works with the old def'n of let 
   (i.e., dynamic binding with no explicit fixpoints). 
-}
evenDef = Abs (Pvar "x") (Cond (Bin IntEq (Var "x") (Const 0)) 
	  	        Tconst
		        (App (Var "odd") (Bin Plus (Var "x") (Const $ -1))))

oddDef =  Abs (Pvar "x") (Cond (Bin IntEq (Var "x") (Const 0)) 
	  	        Fconst
		        (App (Var "even") (Bin Plus (Var "x") (Const $ -1))))


oddeven = Let [(Pvar "even",evenDef),(Pvar "odd",oddDef)] (App (Var "even") (Const 3))

---this one demonstrates irrefutable patterns
---compare with:
---   e1 = App (Abs (redpat "x") (Const 1)) (blackexp (Const 19)) ---> error

irref0 = App (Abs (Pirref (redpat "x")) (Const 1)) (blackexp (Const 19))
irref1 = App (Abs (Pirref (redpat "x")) (Var "x")) (blackexp (Const 19))

v = (z + z) where z = 1 

--- Simple example of a guarded case statement:


c7 = 
   let
	c7body = Match [(Bin IntEq (Var "x") (Var "z"), (Const 99))]
	               [(Pvar "z",(Const 1))]
   in
      Case (Const 1) [(Pvar "x", c7body)]		 


c8 = 
   let
	body = Match [(Bin IntEq (Var "x") (Var "z"), (Const 99))]
	               [(Pvar "z",(Const 2))]
   in
      Case (Const 1) [(Pvar "x", body)]		 

c9 = 
   let
	body = Match [(Bin IntEq (Var "x") (Var "z"), (Const 99))]
	               [(Pvar "z",(Const 1))]
   in
      Case (Const 1) [(Pvar "x", body),(Pvar "y", (Const 101))]		 

c10 = 
   let
	body = Match [(Bin IntEq (Var "x") (Var "z"), (Const 99))]
	               [(Pvar "z",(Const 2))]
   in
      Case (Const 1) [(Pvar "x", body),(Pvar "y", (Const 101))]		 


projy = App (Abs (Ptuple [Pvar "x", Pvar "y", Pvar "z"]) 
		         $ Var "y")
		 (TupleExp [Boom, Const 2, Boom])
