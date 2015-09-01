{-# OPTIONS -fglasgow-exts #-}
{-# LANGUAGE MultiParamTypeClasses, OverlappingInstances, UndecidableInstances, FunctionalDependencies, NoMonomorphismRestriction #-}
{-+
This module defines various auxiliary functions that are used by the type
checker when it needs to refer to things defined in the Prelude, e.g., when
dealing with the do notation, literals, and sections.

These are to considered deprecated now. Since they create hardwired references
to particular original names, they prevent PFE from being used with alternate
Prelude and standard libraries that are structured in differnt ways.
-}
module TiPrelude where
import HsConstants(tuple)
import HasBaseStruct
-- import TiTypes
import TiNames
import HsIdent(HsIdentI)
import HsTypeStruct


--pt :: String->Type
pt :: (HasBaseStruct r (TI i t), TypeCon i) => SrcName -> r
pt n = hsTyCon . prelType $ n

--tBool :: HasBaseStruct t (T t') => t
--tBool :: (HasBaseStruct rec (TI i t), TypeCon i)  => rec
--tBool = pt "Bool"

prelOtherwise = pv "otherwise"
prelFlip   = pv "flip"
{-
prelOtherwise, prelNegate, prelFlip, prelEnumFrom, prelEnumFromTo,
 prelEnumFromThen, prelEnumFromThenTo, prelThen, prelBind, prelFail,
 prelFromInteger, prelFromRational, prelError
 :: ValueId i => HsIdentI i

prelNegate = pv "negate"
prelEnumFrom = pv "enumFrom"
prelEnumFromTo = pv "enumFromTo"
prelEnumFromThen = pv "enumFromThen"
prelEnumFromThenTo = pv "enumFromThenTo"

prelThen = pv ">>"
prelBind = pv ">>="
prelFail = pv "fail"


prelFromInteger = pv "fromInteger"
prelFromRational = pv "fromRational"

prelError = pv "error"
prelEqual = pv "=="
prelGE    = pv ">="
prelPlus  = pv "+"
prelMinus = pv "-"
prelNot   = pv "not"
prelAnd   = pv "&&"
prelOr    = pv "||"

prelFalse = pc "False"
prelNil   = pc "[]"
-}
prelTrue  = pc "True"

--tupleType ts = foldl1 hsTyApp (tuplecon (length ts):ts) :: Type
tupleType ts = hsTyTuple ts -- :: Type
--listType t = hsTyApp (pt "[]") t -- :: Type

tuplecon n = pt (tuple (n-1)) -- :: Type
funcon = pt "->"
