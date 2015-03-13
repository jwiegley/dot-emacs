{-# LANGUAGE DeriveDataTypeable  #-}
-- $Id: HsGuardsStruct.hs,v 1.1 2001/07/25 01:15:30 moran Exp $

module HsGuardsStruct where

import Data.Generics

import SrcLoc1


data HsAlt e p ds
    = HsAlt SrcLoc p (HsRhs e) {-where-} ds
      deriving (Ord,Read, Eq, Show, Data, Typeable)

data HsRhs e
    = HsBody e
    | HsGuard [(SrcLoc, e, e)]
      deriving (Ord,Read, Eq, Show, Data, Typeable)
