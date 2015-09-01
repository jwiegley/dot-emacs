module C2 (module D2, module C2) where
import D2 hiding (main, sq)
sumSquares1 ((x : xs))
    = (sq x) + (sumSquares1 xs) where sq x = x ^ pow
sumSquares1 [] = 0
 