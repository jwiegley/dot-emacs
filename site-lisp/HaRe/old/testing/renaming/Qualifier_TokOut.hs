module Qualifier where

{-Rename 'sumSquares' to 'sum' will fail. The user
  need to qualify the use of 'sum' first. Another
  implemenation option is to let the refactorer qualify
  the use of 'sum' automatically, but the user might overlook
  notice this change.
 -}
sumSquares (x:xs) = sq x + sumSquares xs
    where sq x = x ^pow 
          pow = 2

sumSquares [] = 0

main = sumSquares [1..4] + sum [1..4]
