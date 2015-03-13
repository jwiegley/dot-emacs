-- The trifecta for the K functor.

module HsKindMaps where

import HsKindStruct
import MUtils

mapK f Kstar      = Kstar
mapK f (Kfun x y) = Kfun (f x) (f y)
mapK f Kpred      = Kpred
mapK f Kprop      = Kprop

accK acc ans Kstar          = ans
accK acc ans (Kfun x y)     = acc y (acc x ans)
accK acc ans Kpred          = ans
accK acc ans Kprop          = ans

seqK Kstar      = return Kstar
seqK (Kfun x y) = Kfun # x <# y
seqK Kpred      = return Kpred
seqK Kprop      = return Kprop
