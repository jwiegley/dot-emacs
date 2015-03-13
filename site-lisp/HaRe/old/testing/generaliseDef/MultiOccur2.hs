module MultiOccur2 where

--Generalise the function 'idid' on the first 'id' with a new parameter 'two'

idid = id $ id

main x = idid x
