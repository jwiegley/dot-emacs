module NameResolveIn1 where
f :: [Maybe a] -> [Maybe a] -> [Maybe a]
 
f x y
    =   case y of
            y@[] -> x ++ b_1
            y@(b_3 : b_2) -> x ++ b_1
  where b_1 = x ++ y
f x y = x ++ b_1 where b_1 = x ++ y
 