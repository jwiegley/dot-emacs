module WhereIn3 where

{- A local definition in where clause can be duplicated, it's type signature will also be
   duplicated if there is any. -} 

--In this Example: duplicate the local definition 'x' with name 'xs'

x = 5

foo,bar::Int->Int
foo x= x + 3

--this is comment
bar z = x + y + z
        where
        x,y::Int
        x = 7  
        --This is Comment 
        y = 3  

ram = (let fred = (let x = 5 in x) in fred + x) + 1

main = (foo 1, bar x, ram)