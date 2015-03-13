{-# LANGUAGE ParallelListComp #-}

module Layout.PArr where

blah xs ys = [ (x, y) | x <- xs | y <- ys ]

-- bar = [: 1, 2 .. 3 :]


-- entry point for desugaring a parallel array comprehension

-- parr = [:e | qss:] = <<[:e | qss:]>> () [:():]

{-
ary = let arr1 = toP [1..10]
          arr2 = toP [1..10]
          f = [: i1 + i2 | i1 <- arr1 | i2 <- arr2 :]
          in f !: 1
-}


foo = 'a'

