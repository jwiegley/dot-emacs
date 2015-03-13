module SortProps where
import Sort

assert S0 = {sort []} ::: []

assert S1 = All x . {sort [x]} === {[x]}

assert S2 = All x1 . All x2 . {sort [x1,x2]} === {[x1,x2]}
                           \/ {sort [x1,x2]} === {[x2,x1]}

--assert S = S0 /\ S1 /\ S2

ordered [] = True
ordered [x] = True
ordered (x1:x2:xs) = x1<=x2 && ordered (x2:xs)

lteAll x = all (x<=)

orderedInt :: [Int] -> Bool
orderedInt = ordered 

--property IsTrue = {| x | x===True |}
--property IsOrdered = {|xs | IsTrue {orderedInt xs} |}

property IsOrdered = !ordered

assert InsertProp = All x . All xs . IsOrdered xs ==> IsOrdered {insert x xs}

assert SortProp1 = All xs . IsOrdered {sort xs}

property AllElems P = Gfp X . [] \/ P:X

property Minimal x = AllElems (!((x::Int)<=))

property Or1 P Q = {| x | (x:::P) \/ (x:::Q) |}
property Or2 P Q = P \/ Q

property IsOrdered2 =
   Lfp X . {| xs | (xs:::[]) \/ (Minimal {head xs} xs /\ ({tail xs}:::X)) |}
