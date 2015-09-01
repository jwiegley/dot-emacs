{-# LANGUAGE MultiParamTypeClasses, OverlappingInstances, UndecidableInstances, FunctionalDependencies, NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleInstances #-}
module Products where

toPair1 p   = proj1 p
toPair2 p   = (proj1 p, proj2 p)
toPair3 p   = (proj1 p, proj2 p, proj3 p)
toPair4 p   = (proj1 p, proj2 p, proj3 p, proj4 p)
toPair5 p   = (proj1 p, proj2 p, proj3 p, proj4 p, proj5 p)

class Prod1 p a | p -> a where
    proj1   :: p -> a

class Prod1 p a => Prod2 p a b | p -> b where
    proj2   :: p -> b

class Prod2 p a b => Prod3 p a b c | p -> c where
    proj3   :: p -> c

class Prod3 p a b c => Prod4 p a b c d | p -> d where
    proj4   :: p -> d

class Prod4 p a b c d => Prod5 p a b c d e | p -> e where
    proj5   :: p -> e


infix 8 >< 

fork                :: (x -> a) -> (x -> b) -> x -> (a,b)
(><)                :: (x -> y) -> (a -> b) -> (x,a) -> (y,b)

fork f g x          = (f x, g x)
(f >< g) (x,y)      = (f x, g y)


instance Prod1 (a,b) a where
    proj1 (x,_)         = x

instance Prod1 (a,b,c) a where
    proj1 (x,_,_)       = x

instance Prod1 (a,b,c,d) a where
    proj1 (x,_,_,_)     = x

instance Prod1 (a,b,c,d,e) a where
    proj1 (x,_,_,_,_)   = x


instance Prod2 (a,b) a b where
    proj2 (_,x)         = x

instance Prod2 (a,b,c) a b where
    proj2 (_,x,_)       = x

instance Prod2 (a,b,c,d) a b where
    proj2 (_,x,_,_)     = x

instance Prod2 (a,b,c,d,e) a b where
    proj2 (_,x,_,_,_)   = x


instance Prod3 (a,b,c) a b c where
    proj3 (_,_,x)       = x

instance Prod3 (a,b,c,d) a b c where
    proj3 (_,_,x,_)     = x

instance Prod3 (a,b,c,d,e) a b c where
    proj3 (_,_,x,_,_)   = x


instance Prod4 (a,b,c,d) a b c d where
    proj4 (_,_,_,x)     = x

instance Prod4 (a,b,c,d,e) a b c d where
    proj4 (_,_,_,x,_)   = x


instance Prod5 (a,b,c,d,e) a b c d e where
    proj5 (_,_,_,_,x)  = x


