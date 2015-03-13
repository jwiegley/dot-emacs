module PolymorhicIn1 where


f :: [a] -> a
f ((x : xs))
    =   case xs of
            xs@[] -> x
            xs@(b_1 : b_2) -> x
f ((x : xs)) = x