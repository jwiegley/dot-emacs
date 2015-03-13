module Ite where

{- imports will be added for the PointlessP librasies -}

import PointlessP.Combinators
import PointlessP.RecursionPatterns
import PointlessP.Isomorphisms
import PointlessP.Functors
-- the whole expression will be selected for translation.
notZero = app .
              (((curry
                     (app .
                          ((curry
                                ((((inN (_L :: Bool)) . (Right . bang)) \/
                                      ((inN (_L :: Bool)) . (Left . bang))) .
                                     distr)) /\
                               ((ouT (_L :: Bool)) .
                                    (app .
                                         ((curry
                                               ((((inN (_L :: Bool)) . (Left . bang)) \/
                                                     ((inN (_L :: Bool)) .
                                                          (Right . bang))) .
                                                    distr)) /\
                                              ((ouT (_L :: Int)) . snd))))))) .
                    bang) /\
                   id)
