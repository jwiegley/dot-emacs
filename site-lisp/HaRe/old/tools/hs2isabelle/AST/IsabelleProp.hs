module IsabelleProp where
import IsabelleTerm
import IsabelleType
import Mixfix

type TypedId = (String, Maybe Type)

data Prop
  = PropTrue                                     {- truth value -}
  | PropFalse                                    {- truth value -}
  | PropVar     String                           {- Propositional variable -}
  | PropHas     [PredArg] Pred                   {- Predicate membership -}
  | PropEqual   Term Term                        {- equality assertion -}
  | PropConj    Prop Prop                        {- propositional conjunct -}
  | PropDisj    Prop Prop                        {- propositional disjunct -}
  | PropImpl    Prop Prop                        {- implication chain -}
  | PropEquiv   Prop Prop                        {- equivalence -}
  | PropNeg     Prop                             {- negation -}
  | PropForall  [TypedId] Prop                   {- universal quantification -}
  | PropExists  [TypedId] Prop                   {- existential quantification -}
    -- maybe should add type field to quantifiers

propForall x (PropForall xs u) = PropForall (x:xs) u
propForall x u = PropForall [x] u

propExists x (PropExists xs u) = PropExists (x:xs) u
propExists x u = PropExists [x] u

data PropDecl
  = PropDecl String Prop                {- prop. declaration -}


--signature sorts Pred PredPat PredFormula PredDecl

data Pred
{-  PredConst : String -> Pred -}           {- predicate constant -}
  = PredUniv
  | PredUndef
  | PredArrow   Pred Pred                     {- arrow predicate -}
  | PredLfp     String Pred                   {- least fixed-point predicate -}
  | PredGfp     String Pred                   {- greatest fixed-point predicate-}
  | PredVar     String                        {- predicate variable -}
  | PredLifted  Term                          {- lifted section predicate -}
  | PredNeg     Pred                          {- negated predicate -}
  | PredStrong  Pred                          {- strengthened predicate -}
  | PredTuple   [Pred]                        {- tuple predicate -}
  | PredLit     Integer                       {- literal predicate -}
  | PredCong    String [PredArg]              {- constructor congruence pred. -}
  | PredComp    [Pattern] Prop                {- set comprehension -}
  | PredDisj    Pred Pred                     {- pred. disjunction -}
  | PredConj    Pred Pred                     {- pred. conjunction -}
  | PredImpl    Pred Pred                     {- pred. implication chain -}
  | PredEquiv   Pred Pred                     {- pred. equivalence -}
     -- shouldn't PredEquiv return Prop? or is this pointwise equivalence?

data PredArg
  = TermArg Term
  | PredArg Pred

data PredPat
  = PredAbs String [String]  {- pred. abstraction -}
{-
data Param
  = TermParam String
  | PredParam String
-}
data PredDecl
  = PredDecl PredPat Pred  {- pred. declaration -}

------------------------------------------------------------

instance Show Prop where
  showsPrec p x = case x of
    PropTrue -> showString "PropTrue"
    PropFalse -> showString "PropFalse"
    PropVar x -> showString x
    PropHas [x] a -> mixfix "_ : _" [showsPrec 50 x, showsPrec 51 a] 50 p
    PropHas xs a -> mixfix "_ : _" [showTuple (map shows xs), showsPrec 51 a] 50 p
    PropEqual u v -> mixfix "_ = _" [showsPrec 50 u, showsPrec 51 v] 50 p
    PropConj u v -> mixfix "_ & _" [showsPrec 36 u, showsPrec 35 v] 35 p
    PropDisj u v -> mixfix "_ & _" [showsPrec 31 u, showsPrec 30 v] 30 p
    PropImpl u v -> mixfix "_ --> _" [showsPrec 26 u, showsPrec 25 v] 25 p
    PropEquiv u v -> mixfix "_ = _" [showsPrec 50 u, showsPrec 51 v] 50 p
    PropNeg u -> mixfix "~ _" [showsPrec 40 u] 40 p
    PropForall xs u ->
        mixfix "ALL _. _" [showTypedIds xs, showsPrec 10 u] 10 p
    PropExists xs u ->
        mixfix "EX _. _" [showTypedIds xs, showsPrec 10 u] 10 p
    where
      showTypedId p (x, Nothing) = showString x
      showTypedId p (x, Just t) = mixfix "_::_" [showString x, shows t] 0 p
      showTypedIds (x:[]) = showTypedId 0 x
      showTypedIds (x:xs) = mixfix "_ _" [showTypedId 1 x, showTypedIds xs] 0 0

instance Show Pred where
  showsPrec p x = case x of
    PredUniv -> showString "UNIV"
    PredUndef -> showString "{UU}"
    PredArrow a b -> mixfix "arrow _ _" [showsPrec 1000 a, showsPrec 1000 b] 999 p
    PredLfp x a -> mixfix "lfp (%_. _)" [showString x, shows a] 999 p
    PredGfp x a -> mixfix "gfp (%_. _)" [showString x, shows a] 999 p
    PredVar x -> showString x
    PredLifted x -> mixfix "lifted _" [showsPrec 1000 x] 999 p
    PredNeg a -> mixfix "- _" [showsPrec 81 a] 80 p
    PredStrong a -> mixfix "strong _" [showsPrec 1000 a] 999 p
    PredTuple as -> showTuple (map shows as)
    PredLit n -> showBraces (shows (HInt n))
    PredCong c [] -> showBraces (showString c)
    PredCong c xs -> mixfix "cong_ _ _"
      [shows (length xs), showString c, showSpaceSep (map showCongArg xs)] 999 p
    PredComp [x] a -> mixfix "{_. _}" [shows x, shows a] 1000 p
    PredComp xs a -> mixfix "{_. _}" [showTuple (map shows xs), shows a] 1000 p
    PredDisj a b -> mixfix "_ Un _" [showsPrec 65 a, showsPrec 66 b] 65 p
    PredConj a b -> mixfix "_ Int _" [showsPrec 70 a, showsPrec 71 b] 70 p
    PredImpl a b -> showsPrec p (PredDisj (PredNeg a) b)
    PredEquiv a b -> mixfix "_ <=> _" [showsPrec 50 a, showsPrec 51 b] 50 p

instance Show PredArg where
  showsPrec p x = case x of
    TermArg t -> showsPrec p t
    PredArg a -> showsPrec p a

showCongArg x = case x of
    TermArg t -> showBraces (shows t)
    PredArg a -> showsPrec 1000 a

instance Show PredPat where
  showsPrec p (PredAbs f xs) = case xs of
    [] -> showString f
    _  -> mixfix "_ _" [showString f, showSpaceSep (map showString xs)] 999 p
{-
instance Show Param where
  showsPrec p x = case x of
    TermParam s -> showString s
    PredParam s -> showString s
-}
instance Show PredDecl where
  showsPrec p (PredDecl (lhs@(PredAbs x _)) rhs) =
    mixfix "constdefs\n  _ :: \"\\_\"\n  \"_ == _\"\n"
      [showString x, showsPrec 3 lhs, showsPrec 2 rhs] 2 p

instance Show PropDecl where
  showsPrec p (PropDecl lhs rhs) =
    mixfix "(*\nlemma _: \"_\"\n*)\n" [showString lhs, shows rhs] 0 0
{-
    mixfix "constdefs\n  _ :: bool\n  \"_ == _\"\n"
      [showString lhs, showString lhs, showsPrec 2 rhs] 2 p
-}
