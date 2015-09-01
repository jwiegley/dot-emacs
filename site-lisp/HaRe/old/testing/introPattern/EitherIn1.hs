module EitherIn1 where

import Prelude

-- test introduce patterns
-- select x on lhs of g and introduce patterns for the list type...


g :: [Int] -> Int
g x = head x + tail (head x)