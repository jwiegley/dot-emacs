module EitherIn1 where

import Prelude

-- test introduce patterns
-- select x on lhs of g and introduce patterns for the list type...


g :: [Int] -> Int
g x@[] = (head x) + (tail (head x))
g x@(b_1 : b_2) = (head x) + (tail (head x))
g x = (head x) + (tail (head x))