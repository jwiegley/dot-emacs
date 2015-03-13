module FunIn3 where

--In this example, the let expression  function 'f' is generalised as parameter 'z'
--This example aims to test layout&comments.

f z x y = x + y + z  --This is a comment 

g = f   (let z1 = 10
              
             z2 = 20
         in z1 + z2) 10  20 + f   (let z1 = 10
                                        
                                       z2 = 20
                                   in z1 + z2) 20 40  --This is a comment
 