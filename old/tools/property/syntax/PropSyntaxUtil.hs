module PropSyntaxUtil(module HsConstants,module PropSyntaxUtil) where

import HsConstants
import PropSyntax(hsTyCon,HsType)

-- Built-in type constructors/names

unit_tycon          = hsTyCon unit_tycon_name :: HsType
fun_tycon           = hsTyCon fun_tycon_name :: HsType
list_tycon          = hsTyCon list_tycon_name :: HsType
tuple_tycon i       = hsTyCon $ tuple_tycon_name i :: HsType
