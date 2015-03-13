module PolymorhicIn1 where


f :: [a] -> a
f ((x : xs@[])) = x
f ((x : xs@(b_1 : b_2))) = x
f ((x : xs)) = x