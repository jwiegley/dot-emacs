module Test1 where

--id x = x

--f x = not (not x)
f = not . not

g,h :: a -> a
g x = x
h = g

property IsId = {| f::a->a | All x.  {f x}===x |}

--(x,y)=(id,id)

assert IdIsId = id ::: IsId  {-#cert:IdIsId#-}
assert Id_g = g ::: IsId  {-#cert:Id_g#-}
assert Id_g' = IsId g

assert MapIdIsId = {map id} ::: IsId  {-#cert:MapIdIsId#-}
--property P = P

assert NotNotIsId = f ::: IsId   {-#cert:NotNotIsId#-} {-#cert:NotNotIsId2#-}

property Reflexive = {| rel::a->a->a | All x . { x `rel` x } === {True} |}

assert EqReflBool = {(==)::Bool->Bool->Bool} ::: Reflexive
{-#cert:EqReflBool#-}

allElems :: (Bounded a,Enum a) => [a]
allElems = [minBound..maxBound]
--allElems = [fa,tr]
--all = [False,True]

tr = succ False
fa = pred True

assert AllBools = allElems==={[False,True]}  {-#cert:AllBools#-}


property F = {|b|b==={False}|}
property T = {|b|b==={True}|}
assert ExcludedMiddle = All b . b ::: (F \/ T) {-#cert:ExcludedMiddle#-}
