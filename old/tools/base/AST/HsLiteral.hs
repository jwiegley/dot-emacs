{-# OPTIONS_GHC -cpp  #-}
{-# LANGUAGE DeriveDataTypeable #-}
module HsLiteral where

import Data.Generics

-- import Ratio
--import PrettyPrint
--import SrcLoc

data HsLiteral
    = HsInt         Integer
    | HsChar        Char
    | HsString      String
    | HsFrac        Rational
    -- GHC unboxed literals:
    | HsCharPrim    Char
    | HsStringPrim  String
    | HsIntPrim     Integer
    | HsFloatPrim   Rational
    | HsDoublePrim  Rational
    -- GHC extension:
    | HsLitLit      String
      deriving (Ord, Read, Eq, Show, Data, Typeable)
