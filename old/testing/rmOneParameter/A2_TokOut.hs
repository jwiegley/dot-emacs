module A2 where
 
import D2

sumSq xs ys= sum (map sq xs) + sumSquares xs 

main = sumSq [1..4]

