module A1 where
import C1
import D1
sumSq xs
    =   ((sum (map (sq sq_f) xs)) + (sumSquares xs)) +
	    (sumSquares1 xs)
 
main = sumSq [1 .. 4]
 