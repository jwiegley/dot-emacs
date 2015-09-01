module ListComp1 where

-- even though in a list comprehension
-- should still introduce the runEval in  a let binding...


import Control.Parallel.Strategies (rpar, runEval)

qsort (x:xs) = res
     where res =  [let p_2
                           =
                               runEval
                                   (do p_2 <- rpar p
                                       return p_2)
                   in (p, q) | p <- (filter (< x) xs),
                               q <- (filter (>= x) xs)]