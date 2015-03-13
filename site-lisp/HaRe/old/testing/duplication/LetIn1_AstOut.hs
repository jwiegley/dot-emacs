module LetIn1 where
x = 5
 
foo = x + 3
 
bar z
    = (x + y) + z
  where
      x = 7
      y = 3
 
ram =   (let fred = (let x = 5 in x)
	      
	     dref = (let x = 5 in x)
	 in fred + x) +
	    1
 
main = (foo, bar x, ram)
 