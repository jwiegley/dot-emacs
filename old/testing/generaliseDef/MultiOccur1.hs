module MultiOccur1 where

--Generalise the function 'idid' on the second 'id' with a new parameter 'two'

idid = id $ id

main x = idid x
