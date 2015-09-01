module Test2 where

f =  myMap id "hello"
  where
    myMap h "" = ""
    myMap h (x:xs) = h xs : myMap h xs


