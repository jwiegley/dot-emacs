module B4 () where
import D4 hiding (sumSquares, fringe)
import D4 (fringe)
import C4 hiding (myFringe)
sumSquares ((x : xs)) = (x ^ 2) + (sumSquares xs)
sumSquares [] = 0
 