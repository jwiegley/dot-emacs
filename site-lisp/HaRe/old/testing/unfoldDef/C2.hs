module C2 where 

{-Unfold 'sq' should fail as 'pow', which is used in the definiton of 'sq'
  is not in scope.
-}
import D2 hiding (main,pow)

sumSquares1 (x:xs) = sq x + sumSquares1 xs
 
sumSquares1 [] = 0

