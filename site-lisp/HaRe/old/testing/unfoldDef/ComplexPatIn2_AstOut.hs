module ComplexPatIn2 where
main :: Int
 
main = foo 3
 
foo :: Int -> Int
 
foo x
    =   (h + t) +
	    (snd (let tup@(h, t)
			  = head $ (zip [1 .. x] [3 .. 15])
		  in tup))
  where
      t :: Int
      h :: Int
      tup :: (Int, Int)
      tup@(h, t) = head $ (zip [1 .. x] [3 .. 15])
 