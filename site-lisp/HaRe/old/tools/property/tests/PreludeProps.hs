module PreludeProps where

{-P: {- -}


property Univ      = Gfp X. X
property Undef     = Lfp X. X
property Absurdity = $Undef

assert undefined ::: Undef

property Finite = $ (Lfp P. ([] \/ Univ : $P))

property LeftUnit  op e = All x . {e `op` x} === x
property RightUnit op e = All x. {x `op` e} === x
property Assoc     op   = All x. All y. All z. {(x `op` y) `op` z} === {x `op` (y `op` z)}
property Monoid    op e = Assoc op /\ RightUnit op e /\ LeftUnit op e


property Strict = Undef -> Undef

--assert P1 /\ P1

assert P1 = All x. All y. {const x y} === x
assert All f. All x. {const x . f} === {const x}
assert All f. All x. {f . const x} === {const (f x)}
assert sum === {foldr (+) 0}
assert {sum undefined} === undefined
assert {sum undefined} ::: Undef
assert {sum []} === 0
assert All x. All xs. {sum (x:xs)} === {x + sum xs} 
assert All xs. All ys. {sum (xs ++ ys)} === {sum xs + sum ys}
assert {sum . map length} === {length . concat}
assert length === {sum . map (const 1)}
assert All xs. All ys. {length (xs ++ ys)} === {length xs + length ys}
assert {length undefined} === {undefined}
assert {length []} === 0
assert All x. All xs. {length (x:xs)} === {1 + length xs}
assert length === {foldl (\u us -> 1 + us) 0}

-- assert All xs. Finite xs ==> {length xs} =/= _|_
assert All xs. -/ Finite xs \/ -/ ({length xs} === {undefined})
assert All xs. -/ (Finite xs /\ {length xs} === {undefined})
assert All xs. -/ (Finite xs /\ {length xs} ::: Undef)

assert All xs. Finite xs ==> -/ {length xs} ::: Undef
assert All xs. {length xs} === 0 ==> xs === {[]}

assert All xs. -/ {length xs} === 0 \/ xs === {[]}
assert All xs. -/ {length xs} === 0 \/ xs ::: $[]


assert All f. All xs. {length (map f xs)} === {length xs}
assert All xs. {length (reverse xs)} === {length xs}
assert All f. All a. {foldl f a undefined} === undefined
assert All f. All a. {foldl f a []} === a
assert All f. All a. All x. All xs. {foldl f a (x:xs)} === {foldl f (f a x) xs}
-- assert All f. All a. Monoid f a /\ (All x. {f x undefined} === undefined})
--               /\ (All y. {f undefined y} === undefomed) ===>
--              All xs. {foldr f a xs} === {foldl f a xs}

-- assert All f. All a. Monoid f a /\ (All x. {f x undefined} === undefined})
--               /\ (All y. {f undefined y} === undefomed) ===>
--              All x. All xs. {foldl f xs} === {f x (foldl f a xs)}

-- assert All p. {filter p} === {foldr q []
--    where q x us = if p x then x:us else us}


assert All p. {filter p} === {let q x us = if p x then x:us else us 
                              in foldr q []}

assert All p. {filter p undefined} === undefined
assert All p. {filter p []} === {[]}
assert All p. All xs. All ys. {filter p (xs ++ ys)} === 
                                                {filter p xs ++ filter p ys}
assert All p. {filter p . concat} === {concat . map (filter p)}

-- assert All p. All x. All xs. case {p x} of 
--  undefined   -> {filter p (x:xs)} === undefined
--  {True}      -> {filter p (x:xs)} === {x : filter p xs}
--  {False}     -> {filter p (x:xs) === {filter p xs}

-- assert All p. All x. All xs. {p x} ==> {filter p (x:xs)} === 
--                                                          {x : filter p xs}

assert All p, x, xs. -/ ({p x} ::: $True) 
                     \/ {filter p (x:xs)} === {x : filter p xs}

assert All p, x, xs. {p x} ::: $True ==>
                     {filter p (x:xs)} === {x : filter p xs}

assert All p. All x. All xs. ({p x} ::: False) 
                            \/ {filter p (x:xs)} === {x : filter p xs}

assert All p. All x. All xs. -/ {p x} ::: $False 
                            \/ {filter p (x:xs)} === {filter p xs}

assert All p. All x. All xs. {p x} ::: $False ==>
                             {filter p (x:xs)} === {filter p xs}

assert All p. All x. All xs. {p x} ::: True 
                            \/ {filter p (x:xs)} === {filter p xs}

-- the above assertions use: 
assert All x. (x ::: $True \/ x ::: False) /\ (x ::: True \/ x ::: $False)


rev ys []       = ys
rev ys (u:us)   = rev (u:ys) us
    
assert All ys. {rev ys undefined} === undefined
assert All ys. {rev ys undefined} ::: Undef

assert All ys. {rev ys []} === ys
assert All x. All xs. All ys. {rev ys (x:xs)} === {rev (x:ys) xs}
assert All xs. All ys. {rev ys xs} === {reverse (xs ++ ys)}
assert All xs. {reverse xs} === {rev [] xs}

assert {head undefined} === {undefined}
assert {head undefined} ::: Undef

assert {head []} === undefined
assert {head []} ::: Undef

assert All x. All xs. {head (x:xs)} === x

assert {concat undefined} === undefined
assert {concat undefined} ::: Undef

assert {concat []} === {[]}
assert {concat []} ::: $[]

assert All xs. All xss. {concat (xs:xss)} === {xs ++ concat xss}
assert concat === {foldr (++) []}
assert {concat . concat} === {concat . map concat}

assert All f. All a. Monoid f a ==> {foldr f a . map (foldr f a)} === {foldr f a . concat}

assert All xss. All yss. {concat (xss ++ yss)} === {concat xss ++ concat yss}

assert Monoid (++) {[]}

property NonMono1 = Lfp P. {| x | -/ x ::: P |}

--property NonMono2 Q = Lfp P. {| x | -/ x ::: P /\ (Q P) |}

-- Pred a = a -> Prop ??


------------------------

-- how to write "implies" and "iff" nicely?

-- foldr
assert All f . All a .                  {foldr f a} ::: Undef -> Undef
assert All f . All a .                  {foldr f a []} === a
assert All f . All a . All x . All xs . {foldr f a (x:xs)} === {f x (foldr f a xs)}

assert All f . All a . All xs . All ys . {foldr f a (xs ++ ys)} === {foldr f (foldr f a ys) xs}
assert All xs . All ys .                 {xs ++ ys} === {foldr (:) ys xs}

assert All f . All a .
    (Strict f /\ Monoid f a) ==>
      All xs . All ys . 
                 {foldr f a (xs ++ ys)} === {f (foldr f a xs) (foldr f a ys)}

-- map
assert All f .                  {map f} ::: Undef -> Undef
assert All f .                  {map f []} ::: []
assert All f . All x . All xs . {map f (x:xs)} === {f x : map f xs}

assert All xs . All ys . All f . {map f (xs ++ ys)} === {map f xs ++ map f ys}
assert All xs .                  {map id xs} === xs
assert All f. All g .            {map (f . g)} === {map f . map g}
assert All xs . All f .          {reverse (map f xs)} === {map f (reverse xs)}
assert All xs . All f .          {map f xs} === {[f x | x<-xs]}
assert All f .                   {map f} === {foldr (\u us -> f u : us) []}


-- id, (.)
assert All x . {id x} === x
assert All f . All g . All x . {f (g x)} === {(f . g) x}

assert LeftUnit (.) id
assert RightUnit (.) id
assert Assoc (.)
assert Monoid (.) id

assert Finite {[]}


-- is there a nicer way to write iff?
-- 
--assert All xs . All x . Finite {xs} iff Finite {x:xs}
--assert All xs . All f . Finite {xs} iff Finite {map f xs}
--assert All xs . Finite {xs} iff Finite {reverse xs}
--assert All xs . All ys . Finite {xs ++ ys} iff (Finite {xs} /\ Finite {ys})

assert All xs . All x .  (-/ Finite {xs} \/ Finite {x:xs}) /\ --
                         (-/ Finite {x:xs} \/ Finite {xs})

assert All xs . All x .  Finite {xs} <==> Finite {x:xs}

assert All xs . All f .  (-/ Finite {xs} \/ Finite {map f xs}) /\ 
                         (-/ Finite {map f xs} \/ Finite {xs})

assert All xs . All f .  (Finite {xs} <==> Finite {map f xs})

assert All xs .          (-/ Finite {xs} \/ Finite {reverse xs}) /\ --
                         (-/ Finite {reverse xs} \/ Finite {xs})

assert All xs .          Finite {xs} <==> Finite {reverse xs}

assert All xs . All ys . (-/ Finite {xs ++ ys} \/ (Finite {xs} /\ Finite {ys})) /\ --
                         (-/ (Finite {xs} /\ Finite {ys}) \/ Finite {xs ++ ys})

assert All xs . All ys . Finite {xs ++ ys} <==> (Finite {xs} /\ Finite {ys})



-- reverse
assert                  reverse ::: Undef -> Undef
assert                  {reverse []}     === {[]}
assert All x . All xs . {reverse (x:xs)} === {reverse xs ++ [x]}

assert All xs . {reverse xs} === {[]} ==> xs === {[]}

assert All xs . All ys . -/ (Finite xs) \/ {reverse (ys ++ xs)} === {reverse ys ++ reverse xs}
assert All xs . -/ Finite xs \/ {reverse (reverse xs)} === xs
assert All f . All xs . -/ Strict f \/ {head (map f xs)} === {f (head xs)}
assert All xs . {head (reverse xs)} === {last xs}
assert All xs . {last (reverse xs)} === {head xs}

assert All xs . All f . -/ Strict f                  \/ {last (map f xs)} === {f (last xs)}
assert All xs . All f . -/ (Finite xs /\ -/ xs:::[]) \/ {last (map f xs)} === {f (last xs)}

assert All xs . All f . Strict f ==> {last (map f xs)} === {f (last xs)}
assert All xs . All f . (Finite xs /\ -/ xs:::[]) ==> {last (map f xs)} === {f (last xs)}


-- last
assert last ::: Undef -> Undef
assert last ::: [] -> Undef
assert All x . All xs . {last (x:xs)} === {case xs of { [] -> x; (u:us) -> last (u:us)}}
assert All x . {last [x]} === x
assert All x . All y . All ys . {last (x:y:ys)} === {last (y:ys)}
assert All xs . All ys . -/ Finite xs \/ (ys ::: [] /\ {last (xs ++ ys)} === {last ys})

assert All xs . All ys . Finite xs ==> (ys ::: $[] /\ {last (xs ++ ys)} === {last xs}) 

-}
