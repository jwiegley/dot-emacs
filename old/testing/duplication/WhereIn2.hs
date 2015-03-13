module WhereIn2 where

{- A top level definition can be duplicated, it's type signature will also be
   duplicated if there is any. -} 

--In this Example: duplicate the definition 'foo' with name 'anotherFoo'

x = 5

foo,bar::Int->Int
foo x= x + 3

--this is comment
bar z = x + y + z
        where
        x = 7
        y = 3   --This is comment

ram = (let fred = (let x = 5 in x) in fred + x) + 1

main = (foo 1, bar x, ram)