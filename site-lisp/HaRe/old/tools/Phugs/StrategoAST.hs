module StrategoAST where

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
