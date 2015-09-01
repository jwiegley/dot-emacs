module LiftToTopLevel.Signature where

{- Lifting Baz to the top level should bring in x and a as parameters,
   and update the signature to include these
-}
foo a = baz
  where
    baz :: Int
    baz = x  + a

    x = 1

    y :: Int -> Int -> Int
    y a b = undefined


