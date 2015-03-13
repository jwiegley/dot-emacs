module LiftToTopLevel.Signature3 where

{- Lifting baz to the top level should bring in xx and a as parameters,
   and update the signature to include these
-}
foo a = (baz xx a)
  where
    xx :: Int -> Int -> Int
    xx p1 p2 = p1 + p2




baz:: (Int -> Int -> Int) -> Int ->Int
baz xx a= xx 1 a

