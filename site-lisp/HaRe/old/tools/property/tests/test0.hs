module Test0 where
import List(sort)
import Ix(inRange)
{-P:
import PreludeProps(Finite)
-}

{-P:

property ImpliesToo P Q = -/ P \/ Q

property IsIdentity' = IsIdentity

property IsIdentity f = All x . {f x} === x -- :: Pred(a->a)

property IsIdentityToo f = f === id -- :: Pred(a->a)

assert Id1 = id ::: IsIdentity  {-#cert:id1#-} {-#cert:id1b#-}
assert MapId1 = {map id} ::: IsIdentity  {-#cert:mapid1#-}
-}

idid = id . id

--f x = not (not x)
--f x = not x
f = not . not

testcase1 = print (f True,f False) {-#cert:testcase1#-}

{-P:
assert NotNotIsId = f ::: IsIdentity 
{-#cert:notnot1#-} {-#cert:notnot2#-}

assert not ::: IsIdentity -- unprovable!!

--assert {case True of {True -> id}}:::IsIdentity

-- This style of definition is not supported in Dick's proposed syntax:
--property IsFunctor1 map = All f . All g . {map (f.g)} === {map f . map g}

property IsFunctor1 map = All f . All g . {map (f.g)}==={map f . map g}
property IsFunctor2 map = {map id} === id  -- :: Pred ((a->a)->(b->b))
property IsFunctor      = IsFunctor1 /\ IsFunctor2

assert MF = map ::: IsFunctor
assert IF = id ::: IsFunctor
assert CF = (.) ::: IsFunctor

property AndToo P Q = P /\ Q
property OrToo P Q = P \/ Q

property IsAssoc (*) = All x, y, z . {(x*y)*z} === {x*(y*z)}
property IsCommutative (*) = All x, y . {x*y} === {y*x}

assert PlusAssoc = {(+)::Int->Int->Int} ::: IsAssoc {-#cert:PlusAssoc#-}
assert PlusCommutes = {(+)::Int->Int->Int} ::: IsCommutative

assert PlusAssocFloat = {(+)::Float->Float->Float} ::: IsAssoc {-#cert:PlusAssocFloat#-}

property AC = IsAssoc /\ IsCommutative

assert PlusAC = {(+)::Int->Int->Int} ::: AC {-#cert:PlusAC#-}

--property WO Base pred = Lfp X . {| x | x ::: Base \/ {pred x}::: X |}

--property WO_Int = WO !(==0) {subtract (1::Int)}
-}
fac 0 = 1
fac n = n * fac(n-1)

property InRange r = !(inRange r)

testcase2 = putStr $ unlines [show (n,fac n)|n<-[0..10]] {-#cert:testcase2#-}

{-P:
property Pos x = x::: $ !(>=0)

assert FacPos = {fac::Int->Int} ::: Pos -> Pos {-#cert:FacPos#-}

property PosOp = Pos -> Pos -> Pos
assert PlusPos = {(+)::Int->Int->Int} ::: PosOp {-#cert:PlusPos#-}

--assert fac ::: WO_Int -> WO_Int
-}
x=True

{-P: {--}
property IsTrue = !(==True)
property IsTrueToo = True -- a lifted constructor
-- Are all these equivalent?
assert x==={True}
assert x:::True
assert x::: !(==True)
assert True x
assert x:::IsTrue
assert IsTrue x

--property Finite = Lfp Fin . {| xs | xs:::[] \/ xs::: Univ:Fin |}
--property Finite = Lfp Fin . [] \/ Univ:Fin
--property Infinite = Gfp Inf . {| xs | xs:::Univ:Inf |}
property Infinite = Gfp Inf . Univ:Inf

property Fix P = Lfp X . P X
--u = Univ

-- The predicate that is true for every value:
property Univ = Gfp U . U -- Ok?

assert {[1..10]::[Integer]}:::Finite
assert {[1..]::[Integer]}:::Infinite

assert {Just True} ::: Just True

property LeftUnit m = All x . {fst m x (snd m)} === x

property Eventually P =  Lfp X . ($P : Univ) \/ ($Univ : $X)

property Equal x y = x===y

--property Nub = Lfp Nub . {| x:xs::[a] | True {x `notElem` xs} /\ Nub xs |}

--property InList = Lfp R . {| (x,y:ys) | x === y \/ R {(x,ys)} |}

--property InList2 = Lfp R . {| y:ys,x | x === y \/ R ys x |}

--assert InList {(5, [1..10]::[Integer])}
--assert InList2 {[1..10]::[Integer]} 5
--assert Even1_10 = Exist x . x::: !even ==> x ::: InList2 {[1..10::Integer]}
--assert Even1_10 = Exist x . x::: !even ==> {(x,[1..10::Integer])} ::: InList

property Even = !even
assert ZeroIsEven = 0:::Even

property OldAllElems P = Lfp X . {| xs | xs:::[] \/ xs:::P:X |}
property AllElems P = Lfp X . [] \/ (P:X)
property Minimal ys y = AllElems (!(y<=)) ys
property Ordered = Lfp P . {| xs | xs:::[] \/ xs:::Minimal xs:P |}

xs = [1..60]

assert M = Minimal xs {1}

assert SortProp = All xs.{sort xs}:::Ordered {-#cert:SortProp#-}
assert SortProp2 = {sort::[Int]->[Int]}:::Univ->Ordered {-#cert:SortProp2#-}

assert Fst = All x::Maybe a . x==={Nothing} \/  Exist y . x==={Just y}
{-#cert:Fst#-}
assert Fst' = All x . x ::: (Nothing \/ Just Univ)

property SyntBug = Univ /\ Univ : Univ
property SyntaxBug = {| x | x:::Univ /\ x::: Univ:Univ |}

property Pair = (Univ , Univ)
--property Pair' = {| (x,y) | x:::Univ /\ y:::Univ |}
property Pair'' = (,) Univ Univ
property PosPair = (Pos,Pos)
property Unit = ()

property FiniteToo = $( Lfp P. [] \/ Univ : $P )

assert ExcludedMiddle = All b . b ::: (False \/ True) {-#cert:ExcludedMiddle#-}

property Returns x = {| m | m==={m>>return x} |}

assert RevLength = All xs . {length (reverse xs)} === {length xs}
assert RevSumInt = All xs::[Int] . {sum (reverse xs)} === {sum xs}
assert RevSum = All xs .
   IsCommutative {(+) `at` head xs} ==> {sum (reverse xs)} === {sum xs}

op `at` x = op `asTypeOf` optype x
  where optype :: a -> (a->a->a)
        optype = undefined

-}
