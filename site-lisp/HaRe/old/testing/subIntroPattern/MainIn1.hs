module Main where

data Inf = Nil | Int :* Inf

main 
  = putStrLn $ show (f (1 :* (2 :* ( 3 :* Nil))))


f :: Inf -> Int
f Nil = 0
f (a :* b) = a