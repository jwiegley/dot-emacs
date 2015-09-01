module C2 where
import D2
sumSquares1 ((x : xs))
    = ((sq sq_f) x) + (sumSquares1 xs)
sumSquares1 [] = 0
 
sq_f_1 = 0
 