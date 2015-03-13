module A3 where
 
--Unfold 'sumSquares1'

import C3 

main xs = case xs of 
             [] -> 0
             [x:xs] -> x^pow + (case xs of
                                    (x : xs) -> (sq x) + (sumSquares1 xs)
                                    [] -> 0)

