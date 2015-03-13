module A2 where
 
import D2

sumSq xs ys= sum (map sq xs) + sumSquares xs ys

main = sumSq [1..4]

