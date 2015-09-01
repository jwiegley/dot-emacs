module ScopeAndQual where

import qualified Data.List as L
import Prelude hiding (sum)

main :: IO ()
main = putStrLn (show $ L.sum [1,2,3])

sum a b = a + b

sumSquares xs = L.sum $ map (\x -> x*x) xs

mySumSq = sumSquares
