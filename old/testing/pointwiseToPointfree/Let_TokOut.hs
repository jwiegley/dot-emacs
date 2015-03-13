module Let where

import PointlessP.Functors
import PointlessP.Combinators
import PointlessP.RecursionPatterns
import PointlessP.Isomorphisms
{- imports will be added for the PointlessP librasies -}

-- the whole expression will be selected for translation.
isort =
   app .
       (((app .
              ((curry
                    (app .
                         ((curry
                               (app .
                                    ((curry snd) /\
                                         (fix .
                                              (curry
                                                   (curry
                                                        (app .
                                                             ((curry
                                                                   ((((inN (_L :: [a])) .
                                                                          (Left .
                                                                               bang)) \/
                                                                         (app .
                                                                              ((app .
                                                                                    ((((snd .
                                                                                            fst) .
                                                                                           fst) .
                                                                                          fst) /\
                                                                                         (app .
                                                                                              ((curry
                                                                                                    ((((((((undefined .
                                                                                                                fst) .
                                                                                                               fst) .
                                                                                                              fst) .
                                                                                                             fst) .
                                                                                                            fst) .
                                                                                                           fst) \/
                                                                                                          (fst .
                                                                                                               snd)) .
                                                                                                         distr)) /\
                                                                                                   ((ouT (_L :: [a])) .
                                                                                                        (snd .
                                                                                                             fst)))))) /\
                                                                                   (app .
                                                                                        (((snd .
                                                                                               fst) .
                                                                                              fst) /\
                                                                                             (app .
                                                                                                  ((curry
                                                                                                        ((((inN (_L :: [a])) .
                                                                                                               (Left .
                                                                                                                    bang)) \/
                                                                                                              (snd .
                                                                                                                   snd)) .
                                                                                                             distr)) /\
                                                                                                       ((ouT (_L :: [a])) .
                                                                                                            (snd .
                                                                                                                 fst))))))))) .
                                                                        distr)) /\
                                                                  ((ouT (_L :: Bool)) .
                                                                       (app .
                                                                            ((curry
                                                                                  ((((inN (_L :: Bool)) .
                                                                                         (Left .
                                                                                              bang)) \/
                                                                                        ((inN (_L :: Bool)) .
                                                                                             (Right .
                                                                                                  bang))) .
                                                                                       distr)) /\
                                                                                 ((ouT (_L :: [a])) .
                                                                                      snd)))))))))))) /\
                              (fix .
                                   (curry
                                        (curry
                                             (curry
                                                  (app .
                                                       ((curry
                                                             ((((inN (_L :: [a])) .
                                                                    (Right .
                                                                         (((snd .
                                                                                fst) .
                                                                               fst) /\
                                                                              ((inN (_L :: [a])) .
                                                                                   (Left .
                                                                                        bang))))) \/
                                                                   (app .
                                                                        ((curry
                                                                              ((((inN (_L :: [a])) .
                                                                                     (Right .
                                                                                          ((((snd .
                                                                                                  fst) .
                                                                                                 fst) .
                                                                                                fst) /\
                                                                                               ((snd .
                                                                                                     fst) .
                                                                                                    fst)))) \/
                                                                                    ((inN (_L :: [a])) .
                                                                                         (Right .
                                                                                              ((app .
                                                                                                    ((curry
                                                                                                          (((((((((undefined .
                                                                                                                       fst) .
                                                                                                                      fst) .
                                                                                                                     fst) .
                                                                                                                    fst) .
                                                                                                                   fst) .
                                                                                                                  fst) .
                                                                                                                 fst) \/
                                                                                                                (fst .
                                                                                                                     snd)) .
                                                                                                               distr)) /\
                                                                                                         ((ouT (_L :: [a])) .
                                                                                                              ((snd .
                                                                                                                    fst) .
                                                                                                                   fst)))) /\
                                                                                                   (app .
                                                                                                        ((app .
                                                                                                              (((((snd .
                                                                                                                       fst) .
                                                                                                                      fst) .
                                                                                                                     fst) .
                                                                                                                    fst) /\
                                                                                                                   (((snd .
                                                                                                                          fst) .
                                                                                                                         fst) .
                                                                                                                        fst))) /\
                                                                                                             (app .
                                                                                                                  ((curry
                                                                                                                        ((((inN (_L :: [a])) .
                                                                                                                               (Left .
                                                                                                                                    bang)) \/
                                                                                                                              (snd .
                                                                                                                                   snd)) .
                                                                                                                             distr)) /\
                                                                                                                       ((ouT (_L :: [a])) .
                                                                                                                            ((snd .
                                                                                                                                  fst) .
                                                                                                                                 fst)))))))))) .
                                                                                   distr)) /\
                                                                             ((ouT (_L :: Bool)) .
                                                                                  (app .
                                                                                       ((app .
                                                                                             (((((snd .
                                                                                                      fst) .
                                                                                                     fst) .
                                                                                                    fst) .
                                                                                                   fst) /\
                                                                                                  ((snd .
                                                                                                        fst) .
                                                                                                       fst))) /\
                                                                                            (app .
                                                                                                 ((curry
                                                                                                       ((((((((undefined .
                                                                                                                   fst) .
                                                                                                                  fst) .
                                                                                                                 fst) .
                                                                                                                fst) .
                                                                                                               fst) .
                                                                                                              fst) \/
                                                                                                             (fst .
                                                                                                                  snd)) .
                                                                                                            distr)) /\
                                                                                                      ((ouT (_L :: [a])) .
                                                                                                           (snd .
                                                                                                                fst)))))))))) .
                                                                  distr)) /\
                                                            ((ouT (_L :: Bool)) .
                                                                 (app .
                                                                      ((curry
                                                                            ((((inN (_L :: Bool)) .
                                                                                   (Left .
                                                                                        bang)) \/
                                                                                  ((inN (_L :: Bool)) .
                                                                                       (Right .
                                                                                            bang))) .
                                                                                 distr)) /\
                                                                           ((ouT (_L :: [a])) .
                                                                                snd))))))))))))) /\
                   (fix .
                        (curry
                             (curry
                                  (curry
                                       (app .
                                            ((curry
                                                  ((((inN (_L :: Bool)) .
                                                         (Left . bang)) \/
                                                        (app .
                                                             ((curry
                                                                   ((((inN (_L :: Bool)) .
                                                                          (Right .
                                                                               bang)) \/
                                                                         (app .
                                                                              ((app .
                                                                                    (((((snd .
                                                                                             fst) .
                                                                                            fst) .
                                                                                           fst) .
                                                                                          fst) /\
                                                                                         (app .
                                                                                              ((curry
                                                                                                    ((((inN (_L :: Int)) .
                                                                                                           (Left .
                                                                                                                bang)) \/
                                                                                                          snd) .
                                                                                                         distr)) /\
                                                                                                   ((ouT (_L :: Int)) .
                                                                                                        (((snd .
                                                                                                               fst) .
                                                                                                              fst) .
                                                                                                             fst)))))) /\
                                                                                   (app .
                                                                                        ((curry
                                                                                              ((((inN (_L :: Int)) .
                                                                                                     (Left .
                                                                                                          bang)) \/
                                                                                                    snd) .
                                                                                                   distr)) /\
                                                                                             ((ouT (_L :: Int)) .
                                                                                                  ((snd .
                                                                                                        fst) .
                                                                                                       fst))))))) .
                                                                        distr)) /\
                                                                  ((ouT (_L :: Bool)) .
                                                                       (app .
                                                                            ((curry
                                                                                  ((((inN (_L :: Bool)) .
                                                                                         (Left .
                                                                                              bang)) \/
                                                                                        ((inN (_L :: Bool)) .
                                                                                             (Right .
                                                                                                  bang))) .
                                                                                       distr)) /\
                                                                                 ((ouT (_L :: Int)) .
                                                                                      (snd .
                                                                                           fst)))))))) .
                                                       distr)) /\
                                                 ((ouT (_L :: Bool)) .
                                                      (app .
                                                           ((curry
                                                                 ((((inN (_L :: Bool)) .
                                                                        (Left .
                                                                             bang)) \/
                                                                       ((inN (_L :: Bool)) .
                                                                            (Right .
                                                                                 bang))) .
                                                                      distr)) /\
                                                                ((ouT (_L :: Int)) .
                                                                     (snd .
                                                                          fst))))))))))))) .
             bang) /\
            id)


