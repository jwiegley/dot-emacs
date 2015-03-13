{-# LANGUAGE DeriveDataTypeable #-}
module HsTypeStruct where

import Data.Generics

-------- Types -----------------------------------------------------------------

data TI i t  
    = HsTyFun t t
--  | HsTyTuple [t]
    | HsTyApp t t
    | HsTyVar i
    | HsTyCon i
    | HsTyForall [i] [t] t -- forall is . Ps => t
      deriving (Ord,Eq,Show,Read, Data, Typeable)
