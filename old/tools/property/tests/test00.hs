module Test00 where


property IsIdentity = {| f::a->a | All x . {f x} === x |} -- :: Pred(a->a)

assert Id1 = f ::: IsIdentity  {-#cert:id1#-} {-#cert:id1b#-}

f x = x

assert Str = "ab" === "ab"  {-#cert:string1#-}
assert Int = 1 === 1  {-#cert:int1#-}
assert Plus = {1+1::Integer} === 2 {-#cert:plus1#-} 
assert Plus2 = {1+1==(2::Integer)} ::: True {-#cert:plus2#-} 
assert Sum = {sum [1..10]::Integer}===55 {-#cert:sum1#-} 
