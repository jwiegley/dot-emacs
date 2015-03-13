module TiTest2 where

--id x = x

--length [] = 0

z x = length (id [])

--l xs = length xs

l = \ x y z -> let f x = (x,z)
               in let s = f "hello"
               in (z 'a',f x,f y,s)

ng b x = let f y = if b then x else y
         in (f, f)

{-
id(a::Set) (x::a)::a = x;

length(a::Set)(xs::List a)::Int = Zero@_;

z(a::Set)(b::Set)(x::b)::Int = length a (id (List a) Nil@_);

l(a::Set)(xs::List a)::Int = length a xs;
-}
