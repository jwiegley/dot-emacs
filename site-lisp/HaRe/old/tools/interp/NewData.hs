type Name = String

data Op = Plus | Mult | IntEq | IntLess

data LS = Lazy | Strict

-- M Value
data E
  = Var Name
  | App E E
  | Abs P E
  | Let [D] E
  | Case E [(P,Body,[D])]
  | PairExp E E
  | TupleExp [E]
  | Const Integer
  | ConApp Name [E] -- ConApp Name [(E,Bool)]
  | NewApp Name E
  | Boom
  | Undefined
--- Above is the "core", below various extras
  | Bin Op E E
  | Cond E E E
  | Tconst 
  | Fconst

-- M(Maybe Value)
data Body = Guarded [(E,E)]
           | Normal E

-- M Value -> M(Maybe EnvFrag)
data P = Pconst Integer
       | Pvar Name
       | Ppair P P
       | Ptuple [P]
       | Pcondata Name [P]  
       | Pnewdata Name P
       | Ptilde P

-- M Value -> M Value  OR  EnvFrag
data D = 
   Fun Name [([P],Body,[D])]  -- each item in the list   M Value -> M(Maybe Value)
 | Val P Body [D]  -- EnvFrag
