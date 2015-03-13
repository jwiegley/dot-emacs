module InfixOp where

import PointlessP.Combinators

{- imports will be added for the PointlessP librasies -}


(.+.) _ n m  = n + m

subt _ n m = n - m


-- the whole expression will be selected for translation.
--    it calculates f x y = 2x-2y.
--    Note that all the free variables (of the selected expression) will
--     have a different type after the transformation.
calculate = \x y -> subt ((x .+. x) `subt` y) y
