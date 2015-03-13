module WhereIn1 where

--A top level definition can be duplicated.

--duplicate the definition 'bar' with new name 'sums'

x = 5

foo = x + 3

--this is comment
bar z = x + y + z
        where
        x = 7
        y = 3   --This is comment

--this is comment
sums z = x + y + z
        where
        x = 7
        y = 3   --This is comment

ram = (let fred = (let x = 5 in x) in fred + x) + 1

main = (foo, bar x, ram)