module EitherIn1 where
import Prelude
g :: [Int] -> Int
 
g x@[] = (head x) + (tail (head x))
g x@(b_1 : b_2) = (head x) + (tail (head x))
g x = (head x) + (tail (head x))
 