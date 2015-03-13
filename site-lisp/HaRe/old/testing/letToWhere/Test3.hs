module Test3 where

f h [] = []
f h list = let myMap g [] = []
               myMap g (x:xs) = g x : g xs
           in myMap h list
 