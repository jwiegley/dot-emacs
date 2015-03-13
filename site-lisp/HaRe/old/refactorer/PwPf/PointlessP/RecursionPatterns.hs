{-# OPTIONS -fglasgow-exts #-}

module PointlessP.RecursionPatterns where

import PointlessP.Combinators
import PointlessP.Functors

pmap :: (FunctorOf f d, Rep (f a) fa, Rep (f b) fb) => 
        d -> (a -> b) -> (fa -> fb)
pmap (_::d) f = 
    to . (fmap:: (FunctorOf f d) => (a -> b) -> (f a -> f b)) f . from

hylo :: (FunctorOf f d, Rep (f b) fb, Rep (f a) fa) => 
        d -> (fb -> b) -> (a -> fa) -> a -> b
hylo (_::d) g h = g . pmap (_L::d) (hylo (_L::d) g h) . h

cata :: (FunctorOf f d, Rep (f a) fa, Rep (f d) fd) =>
        d -> (fa -> a) -> d -> a
cata (_::d) f = hylo (_L::d) f out

ana :: (FunctorOf f d, Rep (f a) fa, Rep (f d) fd) =>
       d -> (a -> fa) -> a -> d
ana (_::d) f = hylo (_L::d) inn f

para (_::d) f = 
    hylo (_L :: FunctorOf f d => Mu (PApp f (PProd Id (Const d)))) 
	 f (pmap (_L::d) (id /\ id) . out)

apo (_::d) f = 
    hylo (_L :: FunctorOf f d => Mu (PApp f (PSum Id (Const d))))
	 (inn . pmap (_L::d) (id \/ id)) f

zygo (_::d) g f =
    hylo (_L :: FunctorOf f d => Mu (PApp f (PProd Id (Const a))))
	 f (pmap (_L::d) (id /\ cata (_L::d) g) . out)

paraZygo (_::d) = zygo (_L::d) inn

accum (_::d) t f = 
    hylo (_L :: FunctorOf f d => Mu (PProd f (Const a))) 
	 f ((t /\ snd) . (out >< id))

