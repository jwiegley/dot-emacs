module PointlessP.Isomorphisms where

import PointlessP.Combinators

swap :: (a,b) -> (b,a)
swap = snd /\ fst

coswap :: Either a b -> Either b a
coswap = inr \/ inl

distl :: (Either a b, c) -> Either (a,c) (b,c)
distl = app . ((curry inl \/ curry inr) >< id)

undistl :: Either (a,c) (b,c) -> (Either a b, c)
undistl = inl >< id \/ inr >< id

distr :: (c, Either a b) -> Either (c,a) (c,b)
distr = (swap -|- swap) . distl . swap
--distr = app . ((curry (inl . swap) \/ curry (inr . swap)) >< id) . swap

undistr :: Either (c,a) (c,b) -> (c, Either a b)
undistr = (id >< inl) \/ (id >< inr)

assocl :: (a,(b,c)) -> ((a,b),c)
assocl = id >< fst /\ snd . snd

assocr :: ((a,b),c) -> (a,(b,c))
assocr = fst . fst  /\  snd >< id

coassocl :: Either a (Either b c) -> Either (Either a b) c
coassocl = (inl . inl) \/ (inr -|- id)

coassocr :: Either (Either a b) c -> Either a (Either b c)
coassocr = (id -|- inl) \/ (inr . inr)


unpnt :: (One -> a -> b) -> a -> b
unpnt f = app . (f . bang /\ id)
