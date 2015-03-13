module LiftToTopLevel.Signature3 where

{- Lifting baz to the top level should bring in xx and a as parameters,
   and update the signature to include these
-}
foo a = baz
  where
    baz :: Int
    baz = xx 1 a

    xx :: (Integral t,Num t) => t -> t -> Int
    xx p1 p2 = fromIntegral $ p1 + p2


