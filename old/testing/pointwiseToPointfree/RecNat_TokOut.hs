module RecNat where

import PointlessP.Combinators
import PointlessP.RecursionPatterns
import PointlessP.Isomorphisms
import PointlessP.Functors
{- imports will be added for the PointlessP librasies -}

recNat :: Int -> (Int -> a -> a) -> a -> a
recNat 0 f z = z
recNat n f z = f (n-1) (recNat (n-1) f z)
--Programatica parser can't read:
--   recNat (n+1) f z = f n (recNat n f z)


-- the whole expression will be selected for translation.
-- note that recNat can be converted into a paramorphism because
--  the 2nd and 3rd arguments don't have free variables
double = app .
             (((curry
                    ((para (_L :: Int)
                          (app .
                               (((curry
                                      (app .
                                           ((curry
                                                 ((((inN (_L :: Int)) . (Left . bang)) \/
                                                       (app .
                                                            ((app .
                                                                  ((curry
                                                                        (curry
                                                                             ((inN (_L :: Int)) .
                                                                                  (Right .
                                                                                       ((inN (_L :: Int)) .
                                                                                            (Right .
                                                                                                 snd)))))) /\
                                                                       (snd . snd))) /\
                                                                 (fst . snd)))) .
                                                      distr)) /\
                                                snd))) .
                                     bang) /\
                                    id))) .
                         snd)) .
                   bang) /\
                  id)
