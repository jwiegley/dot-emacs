module MultiOccur2 where

--Generalise the function 'idid' on the first 'id' with a new parameter 'two'

idid two = two $ two

main x = idid id x
