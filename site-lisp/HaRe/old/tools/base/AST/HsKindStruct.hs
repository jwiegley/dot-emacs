{-# OPTIONS_GHC -cpp  #-}
{-# LANGUAGE DeriveDataTypeable #-}
module HsKindStruct where

import Data.Generics

data K x 
    = Kstar    -- base types
    | Kfun !x !x -- higher kinds -- be strict to avoid a space leak
    | Kpred    -- classes
    | Kprop    -- P-logic assertions  & predicates
      deriving (Ord, Eq, Show, Read, Data, Typeable)
