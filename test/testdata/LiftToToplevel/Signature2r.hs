{-# LANGUAGE Rank2Types #-}
module LiftToTopLevel.Signature2 where

{- Lifting baz to the top level should bring in xx and a as parameters,
   and update the signature to include these.

   The refactoring can be completed as the Rank2Types extension is enabled
-}
foo a = baz
  where
    baz :: Int
    baz = xx 1 a

    xx :: (Num t) => t -> t -> t
    xx p1 p2 = p1 + p2


