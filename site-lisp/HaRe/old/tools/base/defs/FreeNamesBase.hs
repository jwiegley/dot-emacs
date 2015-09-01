module FreeNamesBase where

import Syntax(HsDeclI,HsTypeI,HsPatI,HsExpI) 
import FreeNames
import FreeNamesBaseStruct
import DefinedNamesBase

{-+
This module contains just he knot tying definitions for the base syntax.
The reusable instances for the base structure are located in
 #FreeNamesBaseStruct#.
-}

instance Eq i => FreeNames i (HsDeclI i) where freeNames = freeNamesRec
instance Eq i => FreeNames i (HsPatI  i) where freeNames = freeNamesRec
instance Eq i => FreeNames i (HsExpI  i) where freeNames = freeNamesRec
instance Eq i => FreeNames i (HsTypeI i) where freeNames = freeNamesRec
