module ListComp1 where

-- even though in a list comprehension
-- should still introduce the runEval in  a let binding...


qsort (x:xs) = res
     where res =  [ (p,q) | p <- (filter (< x) xs), q <- (filter (>= x) xs) ]