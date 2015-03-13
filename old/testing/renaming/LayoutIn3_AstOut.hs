module LayoutIn3 where
foo x
    =   let anotherX = 12
	in (let y = 3
		 
		z = 2
	    in ((anotherX * y) * z) * w)
  where
      y = 2
      w = x where x = let y = 5 in y + 3
 