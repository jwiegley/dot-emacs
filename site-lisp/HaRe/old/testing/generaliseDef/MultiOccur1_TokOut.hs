module MultiOccur1 where

--Generalise the function 'idid' on the second 'id' with a new parameter 'two'

idid two = two $ two

main x = idid id x
