module SubSubPatternIn2 where

data C1_Type = C1 C2_Type

data C2_Type = C2 Int Int C3_Type

data C3_Type = C3 Int [Int] Int

f :: C1_Type -> Int
f (C1 (C2 x_1 y_2 (C3 x y z))) = z



g :: [Either a b] -> Int
g x@[] = 42
g x@(b_1 : b_2) = 42
g x = 42