module PatternIn3 where
sumSquares y
    =   let x = 1
        in (case x of
                0 -> 0
                x -> x ^ pow) +
               (sq y)
  where
      sq 0 = 0
      sq x = x ^ pow
 
sumSquares_1 y
    =   let x = 1
        in case x of
               0 -> return 0
               x -> return 1
  where
      sq 0 = 0
      sq x = x ^ pow
 
pow = 2
 