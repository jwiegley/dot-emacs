module FunIn4 where

--Default parameters can be added to definition of functions and simple constants.

--In this example: add parameter 'y' to 'foo'

main::Int
main = sum [x+4 |let foo =[1..4], x<-foo]
                          