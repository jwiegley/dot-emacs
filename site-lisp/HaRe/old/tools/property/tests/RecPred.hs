module RecPred where

property Univ = Gfp X . X

property P = [] \/ (Univ : P)
