
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
--                      some examples
-----------------------------------------------------------

redpat = \ x -> Pcondata "red" [(Pvar x)]
greenpat = \ x -> Pcondata "green" [(Pvar x)]
blackpat = \ x -> Pcondata "black" [(Pvar x)]
blackexp = \t -> ConApp "black" [t]
redexp = \t -> ConApp "red" [t]
greenexp = \t -> ConApp "green" [t]
pairpat = Ppair (Pvar "x") (Pvar "y")
black = \ x -> ConApp "black" [x]
red = \ x -> ConApp "red" [x]
green = \ x -> ConApp "green" [x]

--------------------------------------------------

dpat = \ x -> Pcondata "D" [(Pvar x)]
d1 = App (Abs (dpat "i") (Const 42)) Boom
   --- run d1 ==> non-termination
d2 = ConApp "D" [Boom]
   --- run d2 ==> "(D..." + non-termination

npat = \ x -> Pnewdata "N" (Pvar x)
n1 = App (Abs (npat "i") (Const 42)) Boom
   --- run n1 ==> 42 (i.e., 'Abs (npat "i") e' behaves like 'Abs "i" e'

n2 = NewApp "N" Boom
   --- run n2 ==> non-termination

--------------------------------------------------

splat phi = (deM phi (\msg -> error "hey - you're applying the empty env!"))
run le =  (deM (eval le) (\msg -> error "hey - you're applying the empty env!"))

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

irref0 = App (Abs (Ptilde (redpat "x")) (Const 1)) (blackexp (Const 19))
irref1 = App (Abs (Ptilde (redpat "x")) (Var "x")) (blackexp (Const 19))

v = (z + z) where z = 1 


c1 = Case Undefined $ [Normal (Pvar "x") (Const 1) []]     ---> 1
c2 = Case Undefined $ [Normal (Pconst 99) (Const 1) []]    ---> Undefined
c3 = Case Undefined $ [Normal (redpat "x") (Const 1) []]   ---> Undefined
c4 = Case (black Undefined) [Normal (redpat "x") (Const 1) []]
                                                           ---> match failure
c5 = Case (red Undefined) [Normal (redpat "x") (Const 1) []]
                                                           ---> 1
{- c6:
data RBG a = Red a | Black a | Green a
foo = let val = Red (Green 1)
      in
      case val of 
         (Red x) -> (case x of (Black z) -> 99)
         (Red (Green y)) -> 87
-}
c6body = (Case (Var "val") 
            [Normal (redpat "x") 
                    (Case (Var "x") [Normal (blackpat "z") (Const 99) []])
                    [],
            Normal (Pcondata "red" [greenpat "y"]) (Const 87) []])

c6 = Let [(Pvar "val", redexp (greenexp (Const 1)))] c6body

--- Simple example of a guarded case statement:


{-
data Match = Guarded P [(E,E)] [D]
           | Normal P E [D]

c7body = Guarded (Pconst 1)
                         [(Bin IntEq (Const 1) (Const 1), (Const 99))]
                         {- where -} [(Pvar "z",(Const 1))]

c7 = Case (Const 1) [c7body]

-}

c7 = let c7body = Guarded (Pvar "x") 
                          [(Bin IntEq (Var "x") (Var "z"), (Const 99))]  
              {- where -} [(Pvar "z",(Const 1))]
     in Case (Const 1) [c7body]

c8 = let c8body = Guarded (Pvar "x")
                          [(Bin IntEq (Var "x") (Var "z"), (Const 99))]
              {- where -} [(Pvar "z",(Const 2))]
     in Case (Const 1) [c8body]



c9 = 
   let
        guardedbody = Guarded (Pvar "x") 
                              [(Bin IntEq (Var "x") (Var "z"), (Const 99))]
                              [(Pvar "z",(Const 1))]
        normalbody = Normal (Pvar "y")  (Const 101) []
   in
      Case (Const 1) [guardedbody,normalbody]            

c10 = 
   let
        guardedbody = Guarded (Pvar "x") 
                              [(Bin IntEq (Var "x") (Var "z"), (Const 99))]
                              [(Pvar "z",(Const 2))]
        normalbody = Normal (Pvar "y")  (Const 101) []
   in
      Case (Const 1) [guardedbody,normalbody]            

projy = App (Abs (Ptuple [Pvar "x", Pvar "y", Pvar "z"]) 
                         $ Var "y")
                 (TupleExp [Boom, Const 2, Boom])

