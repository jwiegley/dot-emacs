module ListProp where
import List

assert ElemProp = {-#cert:Alfa_ElemProp#-}
  All y . All xs . All ys . True {y `elem` ys} ==> True {y `elem` (xs++ys)}

property Reflexive = {| op | All x . True {op x x} |}

assert NubByProp = {-#cert:Alfa_NubByProp#-}
  All eq . Reflexive {eq} ==> All x . {nubBy eq [x,x]} === {[x]}

sameEq x y = (==) (y `asTypeOf` x)
assert NubProp = {-#cert:Alfa_NubProp#-}
  All x . Reflexive {sameEq x} ==> {nub [x,x]} === {[x]}


assert NubPropDoesn'tWork =
  All x . Reflexive {(==)} ==> {nub [x,x]} === {[x]}
