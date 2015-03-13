
property Foo1 
    =   1 + 2 === 3

property Foo2
    =   True ||| False

property Foo3
    =   not False

property Foo4
    =   (f x === 0) ||| not (f x === 0)


{-
(or
 (/= z (f {+ x {* -1 y}}))
 (/= x {+ z y})
 (= y {+ x {* -1 (f (f z))}})
)
-}

property Foo5 
    =   (not (z === f (x + (-1 * y))))
  |||   (not (x === (z + y)))
  |||   (y === (x + (-1 * (f (f z)))))


{-
(ite
 (and
  (= (f (f (f (f (f x))))) x)
  (= (f (f (f x))) x)
 )
 (= (f x) x)
 true
)
-}

