module Main where

data Inf = Nil | Int :* Inf

main 
  = putStrLn $ show (f (1 :* (2 :* ( 3 :* Nil))))


f :: Inf -> Int
f Nil = 0
f ((a :* b@Nil)) = a
f ((a :* b@(b_1 :* b_2))) = a
f ((a :* b)) = a