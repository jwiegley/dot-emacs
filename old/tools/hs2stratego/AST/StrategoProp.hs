module StrategoProp where
import StrategoTerm
import StrategoPattern
import StrategoType
import Parentheses

--signature  sorts Sequent Rule

data Sequent
  = Valid
  | Consequence ([Prop], [Prop])
  deriving (Show{-,Read-})

data Rule
   = Conclude ([Sequent], Sequent)
  deriving (Show{-,Read-})


--signature   sorts Prop PropDecl Qvar

data Prop
  = True                                         {- truth value -}
  | False                                        {- truth value -}
  | PropVar     (P String)                       {- Propositional variable -}
  | Has         (Term, Pred)                     {- Unary predicate applic. -}
  | HasMult     ([Term], Pred)                   {- k-ary predicate applic. -}
  | Equal       (Term, Term)                     {- equality assertion -}
  | Conj        (P [Prop])                       {- propositional conjunct -}
  | Disj        (P [Prop])                       {- propositional disjunct -}
  | Implies     ([Prop], Prop)                   {- implication chain -}
  | Equiv       (Prop, Prop)                     {- equivalence -}
  | Neg         (P Prop)                         {- negation -}
  | Quant       ([Qvar], Prop)                   {- quantified proposition -}
  deriving (Show{-,Read-})

propVar = PropVar . P
propConj = Conj . P
propDisj = Disj . P
propNeg = Neg . P

data Qvar
  = All         (String, Type)                   {- universal quantification -}
  | Exists      (String, Type)                   {- existential  quantification -}
  deriving (Show{-,Read-})

type Identifier = String -- ??

data PropDecl
  = PropDecl   (Identifier, Prop)                {- prop. declaration -}
  deriving (Show{-,Read-})


--signature sorts Pred PredPat PredFormula PredDecl

data Pred
{-  PredConst : String -> Pred -}           {- predicate constant -}
  = Univ
  | UnDef
--  Just        Pred                          {- case match predicate -}
--  Nothing                                   {- match failure predicate -}
  | Arrow       (Pred, Pred)                  {- arrow predicate -}
  | LfpPred     (String, Pred)                {- least fixed-point predicate -}
  | GfpPred     (String, Pred)               {- greatest fixed-point predicate-}
--  PredRef     Identifier                    {- predicate reference ? -}
  | PredVar     (P Identifier)                {- predicate variable -}
  | LiftedSec   (P Term)                      {- lifted section predicate -}
--  PredSect    Pred * Int                    {- predicate section  (1 or 2) -}
  | PredNeg     (P Pred)                      {- negated predicate -}
  | Strong      (P Pred)                      {- strengthened predicate -}
--  TypedPred   Pred * Type                   {- explicitly typed predicate -}
  | TuplePred   (P [Pred])                    {- tuple predicate -}
  | LitPred     (P Int)                       {- literal predicate -}
  | DataCong    (String, [PredArg])           {- constructor congruence pred. -}
--  PredInst    String * [Term]               {- predicate instance -}
  | Comprehension ([Pattern], Prop)           {- set comprehension -}
  | PredDisj    (P [Pred])                    {- pred. disjunction -}
  | PredConj    (P [Pred])                    {- pred. conjunction -}
  | PredImpl    ([Pred], Pred)                {- pred. implication chain -}
  | PredEquiv   (Pred, Pred)                  {- pred. equivalence -}
  deriving (Show{-,Read-})

predVar = PredVar . P
liftedSec = LiftedSec . P
predNeg = PredNeg . P
strong = Strong . P
tuplePred = TuplePred . P
litPred = LitPred . P
predDisj = PredDisj . P
predConj = PredConj . P

data PredArg
  = TermArg (P Term)
  | PredArg (P Pred)
  deriving (Show)

termArg = TermArg . P
predArg = PredArg . P

data PredPat
  = PredAbs    (String, [Param])  {- pred. abstraction -}
  deriving (Show{-,Read-})

data Param
  = TermParam (P String)
  | PredParam (P String)
  deriving (Show)

termParam = TermParam . P
predParam = PredParam . P

data PredDecl
  = PredDecl   (PredPat, Pred)            {- pred. declaration -}
  deriving (Show{-,Read-})
