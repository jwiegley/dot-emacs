{-# OPTIONS_GHC -cpp  #-}
{-# LANGUAGE DeriveDataTypeable #-}
module HsAssocStruct where

import Data.Generics

-- Formerly known as InfixAssoc...
data HsFixity = HsFixity HsAssoc Int deriving (Ord,Eq,Show,Read, Data, Typeable)

data HsAssoc
    = HsAssocNone
    | HsAssocLeft
    | HsAssocRight
      deriving (Ord, Eq, Show, Read, Data, Typeable)
