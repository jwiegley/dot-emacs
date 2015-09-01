module C2 where
import D2 hiding (main)
sumSquares1 ((x : xs)) = (x ^ pow) + (sumSquares1 xs)
sumSquares1 [] = 0
 