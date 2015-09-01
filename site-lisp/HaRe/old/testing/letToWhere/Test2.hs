module Test2 where

f = let myMap h "" = ""
        myMap h (x:xs) = h xs : myMap h xs
     in myMap id "hello"


