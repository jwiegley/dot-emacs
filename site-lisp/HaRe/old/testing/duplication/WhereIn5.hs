module WhereIn5 where

--In this Example: duplicate the local definition 'foo' with new name 'AnotherFoo' will fail. 

x = 5

foo,bar::Int->Int
foo x= x + 3

--this is comment
bar z = x + y + z
        where
        y::Intes
        y = 3  

ram = (let fred = (let x = 5 in x) in fred + x) + 1

main = (foo 1, bar x, ram)