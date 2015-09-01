module LiftToTopLevel.Signature3 where

{- Lifting baz to the top level should bring in xx and a as parameters,
   and update the signature to include these
-}
foo a = baz
  where
    baz :: Int
    baz = xx 1 a

    xx :: Int -> Int -> Int
    xx p1 p2 = p1 + p2


