module EitherIn2 where

import Prelude

-- test introduce patterns
-- select x on lhs of g should give error as Int is
-- a built in type.

g :: Int -> Int
g x = head x + tail (head x)