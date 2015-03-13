{-# OPTIONS -fglasgow-exts #-}
{-# LANGUAGE MultiParamTypeClasses, OverlappingInstances, UndecidableInstances, FunctionalDependencies, NoMonomorphismRestriction #-}
module DefinedNamesBase(module DefinedNames) where
			-- all instances are exported anyway...
import Syntax(HsDeclI,HsTypeI,HsPatI)
import DefinedNames
import DefinedNamesBaseStruct()

{-+
This module contains just the knot tying definitions for
the base syntax. The reusable instances for the base structure
are located in DefinedNamesBaseStruct.
-}

instance DefinedNames i    (HsDeclI i) where definedNames = definedNamesRec
instance ClassMethods i    (HsDeclI i) where classMethods = classMethodsRec
instance MapDefinedNames i (HsDeclI i) where mapDefinedNames= mapDefinedNamesRec
instance DefinedNames i    (HsPatI  i) where definedNames = definedNamesRec
instance MapDefinedNames i (HsPatI  i) where mapDefinedNames= mapDefinedNamesRec

-- Only for type patterns:
instance DefinedNames i (HsTypeI i) where  definedNames = definedNamesRec

instance AddName i (HsDeclI i) where addName = addNameRec

instance ContextSize [a] where contextSize = length
