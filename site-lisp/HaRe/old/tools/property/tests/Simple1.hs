module Simple1(C) where


data List a   = Nil | Cons a (List a)

-- ?
data TestR a  = TestR { filed1 :: a, field2 :: [a] }

f x = let assert {x > 5} ::: True in 3

data C = Mk



property Any  = Gfp X. X
property None = Lfp X. X

assert All x::Int. x ::: Any
assert Exist x::Int. x ::: None
assert All x::Int. x ::: !even
assert All x::Int. (x ::: !even) \/ x === 1

assert All x. {x::Int} ::: !even ==> -/ (x ::: !odd)
assert A = All x. Exist y. {x::Int} === y  {-#cert:certA#-} {-#cert:certA1#-}

assert B = All xs. {xs::[Int]} ::: !(\xs -> length xs < 3) ==> xs === {[1,2,3,4]}
assert C = All xs. {xs::[Int]} ::: !(\xs -> length xs < 100)

-- signatures in comprahensions don;t yet work in quick check
property AllEven = Gfp X. {| xs :: [Int] | ({xs::[Int]} ::: []) \/ (xs ::: (!even : X)) |}

-- assert D = {[2::Int,4,6,8,10,12]} ::: AllEven
assert E = All xs::[Int]. xs ::: AllEven


assert F = All x::Int. All y. x ::: !(< y) ==> {x + 1} ::: !(<= y)
--assert G = ALl x::Int. x ::: !(const False) ==> undefined

-- assert F = All x::a. x === x
