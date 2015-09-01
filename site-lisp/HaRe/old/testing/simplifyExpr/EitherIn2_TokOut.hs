module EitherIn2 where

-- | Case analysis for the 'Either' type.
-- If the value is @'Left' a@, apply the first function to @a@;
-- if it is @'Right' b@, apply the second function to @b@.
-- either                  :: (a -> c) -> (b -> c) -> Either a b -> c
-- either f _ (Left x)     =  f x
-- either _ g (Right y)    =  g y



f :: Either a a -> a
f x@(Left b_1) = (case (id, id, x) of
                      (f, g, (Left x)) -> f x
                      (f, g, (Right y)) -> g y)
f x@(Right b_1) = (id b_1)
f x = either id id x


p x@(y:ys) = case x of
             [] -> 42
             (z:zs) -> zs


