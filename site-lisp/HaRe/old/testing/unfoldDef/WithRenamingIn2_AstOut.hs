module WithRenamingIn2 where
sumSquares pow y
    = (let pow_1 = 2 in pow ^ pow_1) + (sq y)
 
sq x = x ^ pow where pow = 2
 