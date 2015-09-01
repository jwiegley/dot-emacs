module WhereIn4 where

--In this Example: duplicate the local definition 'y' with new name 'x' will fail. 

x = 5

foo,bar::Int->Int
foo x= x + 3

--this is comment
bar z = x + y + z
        where
        y::Int
        y = 3  

ram = (let fred = (let x = 5 in x) in fred + x) + 1

main = (foo 1, bar x, ram)