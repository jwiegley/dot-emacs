module A1 where

data T1 a b = C1 a b | C2 b a

data T2 a = C3 a

f :: T1 a b -> a
f (C1 x y) = x
f (C2 y x) = x

goo :: T1 a b -> Int
goo (C1 _ _) = 42

res = x
       where
         (C1 x y) = (C1 1 2) 

res1 = let f :: T1 a b -> b 
           f (C1 x y) = y 
           -- f _ = undefined
       in f (C1 1 2)

res2 =  [ f (C1 1 2) | let f (C1 x y) = [1 + 2]]

g x = transform x
       where
        transform :: T1 a b -> T2 a
        transform (C1 x y) = C3 x
        -- transform _ = undefined

h = "ordinary, really"

caseIt x = case x of 
            42 -> f (C1 1 2) 
                    where
                     f (C1 o p )= 56
                     f x = x
            _  -> 42 


{- aMonad 
  = do
       let f :: T1 Int Int -> Int
           f (C1 d c) = 43
           f (C2 k j) = 0
       return (f (C1 2 3)) -}
