module Test3 where

f h [] = []
f h list = myMap h list
    
    where
      myMap g [] = []
      myMap g ((x : xs)) = (g x) : (g xs)
 