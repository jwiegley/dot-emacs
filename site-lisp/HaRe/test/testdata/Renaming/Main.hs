module Main where

--Rename 'main' will fail.

sumSquares (x:xs) = sq x + sumSquares xs
    where sq x = x ^pow 
          pow = 2

sumSquares [] = 0

main=return $ sumSquares [1..4]
