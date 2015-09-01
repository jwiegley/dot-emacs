module FunIn3 where

--In this example, the let expression  function 'f' is generalised as parameter 'z'
--This example aims to test layout&comments.

f x y = x + y + (let z1 = 10
                     z2 = 20
                 in z1 +z2)  --This is a comment 

g = f 10  20 + f 20 40  --This is a comment
 