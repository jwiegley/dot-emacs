{-# OPTIONS -fglasgow-exts #-}

module PointlessP.Combinators where

-- Point free programming combinators

_L :: a
_L = undefined

-- The final object

data One

instance Show One
    where show _ = "_L"

bang :: a -> One
bang _ = _L

-- Products

infix 6  /\
(/\) :: (a -> b) -> (a -> c) -> a -> (b,c)
(/\) f g x = (f x, g x)

infix 7  ><
(><) :: (a -> b) -> (c -> d) -> (a,c) -> (b,d)
f >< g = f . fst /\ g . snd

-- Sums

inl :: a -> Either a b
inl = Left

inr :: b -> Either a b
inr = Right

infix 4 \/
(\/) :: (b -> a) -> (c -> a) -> Either b c -> a
(\/) = either

infix 5 -|-
(-|-) :: (a -> b) -> (c -> d) -> Either a c -> Either b d
f -|- g = inl . f \/ inr . g

infix 5 <>
(<>) :: (a -> b) -> (c -> d) -> Either a c -> Either b d
(<>) = (-|-)

-- Exponentials

app :: (a -> b, a) -> b
app (f,x) = f x

infix 0 !
(!) :: a -> b -> a
(!) = const

-- Points

pnt :: a -> One -> a
pnt x = \_ -> x
 
-- Guards

grd :: (a -> Bool) -> a -> Either a a
grd p x = if p x then inl x else inr x

(?) :: (a -> Bool) -> a -> Either a a
(?) = grd
