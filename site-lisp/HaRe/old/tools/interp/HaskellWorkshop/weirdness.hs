module Weirdness where

{- These are examples of the dark corners of Haskell -}

newtype FooStrict = FooStrict Int 
data FooLazy = FooLazy Int 



omega :: Int->Int
omega x = if True then (omega x) else (omega x)

fooS x = (\ (FooStrict n) -> 1) x
fooL x = (\ (FooLazy n) -> 1) x

ex1 = fooS (FooStrict (omega 2))
ex2 = fooL (FooLazy (omega 2))

bot = bot

data D1 = D1 Int
d1 (D1 i) = 42
ex3 = d1 bot
ex5 = D1 bot

newtype N = N Int
n (N i) = 42
ex4 = n bot
ex6 = N bot


{-

I'm not sure this is an interesting example.

Weirdness> fooS undefined
1
Weirdness> fooL undefined

Program error: {undefined}

Weirdness> fooL (FooLazy (omega 9))
1
Weirdness> fooS (FooStrict (omega 9))
1
-}

{- Here's an example of guards forcing a computational increment -}
data RB = Red Int | Black Int

guard = case (Red (omega 9)) of
          Red x -> "red"
          Black x -> "black"
    --->   "red"

guard' = case (Red (omega 9)) of
          Red x | x==10 -> "red"
          Black x -> "black"
    ---> non-termination

g (Red x) | x==10 = "red"
g (Black x) = "black"

xy | null xy = [1]
   | True = [1,2,3]
   


{-


-} 


{---------------------------------------------------------------------
                        Too much sugar will rot your teeth.
                        The following is an example of a 
                        semantically un-innocent transformation
 ---------------------------------------------------------------------}


{-
nodups [] = []
nodups [x] = [x]
nodups (y:(x:xs)) = if x==y then (nodups (x:xs)) else (y:(nodups (x:xs)))
-}

nodupsNP l = case l of
                [] -> []           
                [x] -> [x]
                (y:(x:xs)) -> if x==y then 
                                (nodupsNP (x:xs)) 
                             else (y:(nodupsNP (x:xs)))

nodups xs'' = case xs'' of
                [] -> []           
                x':xs' -> 
                       case xs' of
                         [] -> [x']
                         x:xs -> if x'==x then 
                                       (nodups (x:xs)) 
                                 else (x':(nodups (x:xs)))



