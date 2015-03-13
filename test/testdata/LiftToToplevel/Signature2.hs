module LiftToTopLevel.Signature2 where

{- Lifting baz to the top level should bring in xx and a as parameters,
   and update the signature to include these.

   The refactoring cannot be attempted as the resulting signature
   requires Rank2Types

    baz:: (forall t. Num t => t -> t -> t) -> Int ->Int
    baz :: Num a => (a -> t1 -> t) -> t1 -> t
    baz xx a= xx 1 a

-}
foo a = baz
  where
    baz :: Int
    baz = xx 1 a

    xx :: (Num t) => t -> t -> t
    xx p1 p2 = p1 + p2


