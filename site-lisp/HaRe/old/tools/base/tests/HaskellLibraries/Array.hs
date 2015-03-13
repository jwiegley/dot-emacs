module  Array ( 
    module Ix,  -- export all of Ix 
    Array, array, listArray, (!), bounds, indices, elems, assocs, 
    accumArray, (//), accum, ixmap ) where

import Prelude
import Ix
import List( (\\) )

infixl 9  !, //

data (Ix a) => Array a b = MkArray (a,a) (a -> b)

--array       :: (Ix a) => (a,a) -> [(a,b)] -> Array a b
array b ivs =
    if and [inRange b i | (i,_) <- ivs]
        then MkArray b $
                     \j -> let vs = [v | (i,v) <- ivs, i == j]
                           in case vs of
                                [v]   -> v
                                []    -> error "Array.!: undefined array element"
                                _     -> error "Array.!: multiply defined array element"
                     
        else error "Array.array: out-of-range array association"

--listArray             :: (Ix a) => (a,a) -> [b] -> Array a b
listArray b vs        =  array b (zipWith (\ a b -> (a,b)) (range b) vs)

(!)                   :: (Ix a) => Array a b -> a -> b
(!) (MkArray _ f)     =  f

bounds                :: (Ix a) => Array a b -> (a,a)
bounds (MkArray b _)  =  b

indices               :: (Ix a) => Array a b -> [a]
indices               =  range . bounds

elems                 :: (Ix a) => Array a b -> [b]
elems a               =  [a!i | i <- indices a]

assocs                :: (Ix a) => Array a b -> [(a,b)]
assocs a              =  [(i, a!i) | i <- indices a]

--(//)                  :: (Ix a) => Array a b -> [(a,b)] -> Array a b
a // us               =  array (bounds a)
                            ([(i,a!i) | i <- indices a \\ [i | (i,_) <- us]]
                             ++ us)

--accum                 :: (Ix a) => (b -> c -> b) -> Array a b -> [(a,c)]
--                                   -> Array a b
accum f               =  foldl (\a (i,v) -> a // [(i,f (a!i) v)])

--accumArray            :: (Ix a) => (b -> c -> b) -> b -> (a,a) -> [(a,c)]
--                                   -> Array a b
accumArray f z b      =  accum f (array b [(i,z) | i <- range b])

--ixmap                 :: (Ix a, Ix b) => (a,a) -> (a -> b) -> Array b c
--                                         -> Array a c
ixmap b f a           = array b [(i, a ! f i) | i <- range b]


instance  (Ix ix)         => Functor (Array ix) where
    fmap fn (MkArray b f) =  MkArray b (fn . f) 

instance  (Eq a,Ix a, Eq b)  => Eq (Array a b)  where
    a == a'             =  assocs a == assocs a'

instance  (Ix a,Ord a, Ord b) => Ord (Array a b)  where
    a <=  a'            =  assocs a <=  assocs a'

instance  (Ix a, Show a, Show b) => Show (Array a b)  where
    showsPrec p a = showParen (p > 9) (
                    showString "array " .
                    shows (bounds a) . showChar ' ' .
                    shows (assocs a)                  )

instance  (Eq a,Ix a, Read a, Read b) => Read (Array a b)  where
    readsPrec p = readParen (p > 9)
           (\r -> [(array b as, u) | ("array",s) <- lex r,
                                     (b,t)       <- reads s,
                                     (as,u)      <- reads t   ])
