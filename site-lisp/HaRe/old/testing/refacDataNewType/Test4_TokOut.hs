module Test4 where

data Dummy = Bob Int
           | Bob2 String

newtype Test = Con String

f 42 = Con "Hello"
