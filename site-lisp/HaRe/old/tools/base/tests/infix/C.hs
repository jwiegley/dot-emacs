module C where
import B

x = a+b*c+d*e^f^g

y = (x , a+b*c+d*e^f^g)
  where
    infixl 0 ^
    a^b=undefined
    y = (x , a+b*c+d*e^f^g)

z = do x <- a+b*x^9
       (+) <- blaha
       x <- a+b*x^9
       let infix 4 ^
	   (^) = bla
       x <- a+b*x^9
       return x
