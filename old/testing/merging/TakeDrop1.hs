module TakeDrop1 where

import Prelude hiding (take, drop)


{- splitat :: Int  ->  [a]  ->  ([a], [a]) -}
splitat 0 xs = ([], xs)
splitat _ [] = ([], [])
splitat n ((x : xs))
    | n > 0 = (x : (take (n - 1) xs), drop (n - 1) xs)
splitat _ _
    =   (error "PreludeList.take: negative argument",
         error "PreludeList.drop: negative argument")
take :: Int -> [a] -> [a]
take 0 xs = []
take _ []= []
take n (x:xs)
  | n > 0 = x : take (n-1) xs
take _ _ = error "PreludeList.take: negative argument"

drop :: Int -> [a] -> [a]
drop 0 xs            = xs
drop _ []            = []
drop n (x:xs) | n>0  = drop (n-1) xs
drop _ _             = error "PreludeList.drop: negative argument"