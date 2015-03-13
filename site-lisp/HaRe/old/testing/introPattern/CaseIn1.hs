module CaseIn1 where

f :: [Int] -> Int
f y = case y of
        _ -> hd y + hd (tl y)

hd x = head x
tl x = tail x
