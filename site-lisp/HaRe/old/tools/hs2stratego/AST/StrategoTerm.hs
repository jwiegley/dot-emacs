module StrategoTerm where
import StrategoPattern
import StrategoType
import Parentheses

data Term
  = HVar (P String)
  | HLit (P Literal)
{- old
  | HLit (P Integer)
  | HCharLit (P Char)
  | HStringLit (P String)
-}
  | HNeg (P Integer) -- just for negated literals
  | HApp (Term, Term)
  | HTuple (P [Term])
  | HCon (String, [Term])
  | HAbs (Pattern, Term) -- should probably be [Pattern]
  | HLet ([Def], Term)
  | HCase (Term, [HBranch])
  | HIte (Term, Term, Term) -- if-then-else
  | HCompose (Term, Term) -- not used
  | TypedVar (String, Type)
  | HConst (P String)             -- Skolem constant
    {- Let is introduced for primarily for alpha conversion.
       It represents an explicit substitution                -}
  | Let  ([Binding], Term)
  deriving (Show{-,Read-})

hVar = HVar . P
hLit = HLit . P
--hCharLit = HCharLit . P
--hStringLit = HStringLit . P
hNeg = HNeg . P
hTuple = HTuple . P
hConst = HConst . P

hlet [] e = e
hlet ds e = HLet (ds,e)

happ = curry HApp
habs1 = curry HAbs
habs ps e = foldr habs1 e ps
-- Wrong strictness, \ p1 p2 -> e is not the same as \ p1 -> \ p2 -> e !!!


-- List constructors:
hlist = foldr hcons hnil
  where hcons x xs = HCon ("Prelude.:", [x,xs])
        hnil = HCon ("[]", [])

-- Sections
hleftsection x op = hVar op `happ` x
hrightsection op y = HAbs (zp, hVar op `happ` ze `happ` y)
hconleftsection x op = HAbs (zp,HCon (op,[x,ze])) -- constructor arity?
hconrightsection op y = HAbs (zp, HCon (op, [ze,y])) -- constructor arity?

z = "zzz"
zp = varPat z
ze = hVar z

nomatch = hVar "Prelude.undefined"

data HBranch
  = HBranch (Pattern, [GuardedTerm]) -- ??
  deriving (Show{-,Read-})

data Def
  = HDef (Pattern, Term)          -- Not quite right; should be an App-Pattern
				  -- but we assume defns are put into a normal
				  -- form by explicit abstraction on the rhs.
  | TSyn (String,[String],Type)
  | TData (String,[String],[DataDecl])
  | TNew (String,[String],DataDecl)
  deriving (Show{-,Read-})

tSyn (c,vs) t = TSyn (c,vs,t)
tData (c,vs) cons = TData (c,vs,cons)
tNew (c,vs) con = TNew (c,vs,con)

data Binding
  = Elt (String, Term)
  deriving (Show{-,Read-})

data GuardedTerm
  = Guarded (Term, Term)
  | NonGuarded (P Term)
  deriving (Show{-,Read-})

nonGuarded = NonGuarded . P

{-
data AbsPat
  = AbstArrow (Pattern, [GuardedTerm])
  deriving (Show{-,Read-})
-}
