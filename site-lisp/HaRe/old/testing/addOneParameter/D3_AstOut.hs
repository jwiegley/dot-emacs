module D3 (sumSquares, sumSquares_y) where
sumSquares y ((x : xs))
    = (sq x) + ((sumSquares y) xs)
sumSquares y [] = 0
 
sumSquares_y = undefined
 
sq x = x ^ pow
 
pow = 2
 