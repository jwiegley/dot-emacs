module FSM(NFA(..),Edge(..),Trans(..),State(..),Map(..),compileRegExp) where
import RegExp
import qualified IntMap as M

-- The representation of (nondeterministic) Finite State Machines:

type Map a = M.IntMap a

type State = Int
data Edge t = E | T t deriving (Eq,Ord,Show)
newtype NFA t = NFA (Map [(Edge t,State)]) deriving (Show)

empty = NFA M.empty

-- Compilation of Regular Expressions into Finite State Machines:

compileRegExp :: RegExp t -> ((State,State),NFA t)
compileRegExp re = run (compile0 re) empty

compile0 re =
  do s <- newstate
     g <- newstate
     compile s g re
     return (s,g)

compile s g re =
     case re of
       Zero -> return ()
       One -> addedge s E g
       S t -> addedge s (T t) g
       re1 :& re2 ->
         do b <- newstate
	    compile s b re1
	    compile b g re2
       re1 :! re2 ->
         do compile s g re1
	    compile s g re2
       re1 :-! re2 -> compile s g re1 -- !!
       Many re ->
         do b <- newstate
	    addedge s E b
	    compile b b re
	    addedge b E g
       Some re ->
         do (s',g') <- compile0 re
	    addedge s E s'
	    addedge g' E s' 
	    addedge g' E g

-- A Regular Expression Compiler Monad:
-- (It's a state monad, where the state contains the next unused state
--  and the machine generated so far.)

newtype Compile t a = C (State -> NFA t -> (a,State,NFA t))

newstate :: Compile t State
newstate = C $ \ n (NFA m) -> (n,n+1,NFA m)

addedge s e g = C $ \ n (NFA m) -> ((),n,NFA (addedge m))
  where
    addedge m = M.add_C (++) (s,[(e,g)]) m

run (C c) fsm = 
  case c 1 fsm of
    (ans,_,fsm) -> (ans,fsm)

instance Monad (Compile t) where
  return x = C $ \ n fsm -> (x,n,fsm)

  C m1 >>= xm2 =
    C $ \ n0 fsm0 -> case m1 n0 fsm0 of
                   (a,n1,fsm1) ->
		     case xm2 a of
		       C m2 -> m2 n1 fsm1
