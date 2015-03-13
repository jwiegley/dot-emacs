module InfixOp where

import PointlessP.Combinators
import PointlessP.Functors
import PointlessP.RecursionPatterns
import PointlessP.Isomorphisms
{- imports will be added for the PointlessP librasies -}


(.+.) _ n m  = n + m

subt _ n m = n - m


-- the whole expression will be selected for translation.
--    it calculates f x y = 2x-2y.
--    Note that all the free variables (of the selected expression) will
--     have a different type after the transformation.
calculate = app .
                (((curry
                       (curry
                            (app .
                                 ((app .
                                       (((subt . fst) . fst) /\
                                            (app .
                                                 ((app .
                                                       (((subt . fst) . fst) /\
                                                            (app .
                                                                 ((app .
                                                                       ((((.+.) . fst) .
                                                                             fst) /\
                                                                            (snd . fst))) /\
                                                                      (snd . fst))))) /\
                                                      snd)))) /\
                                      snd)))) .
                      bang) /\
                     id)
