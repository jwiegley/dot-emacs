{-+
All of the built-in entities that don't contain any recursive parts (mainly
names). 
-}
module HsConstants(module HsConstants,module SpecialNames,HsName) where

import HsName
import HsIdent
import SpecialNames


-- The module that is implicitly imported in all modules: ----------------------
prelude_mod_name' = "Prelude"
mod_Prelude'      = plainModule prelude_mod_name'


-- Module names for constructing original names of standard entities: ----------
--{ -
-- For use with PFE libraries:
mod_Prelude      = plainModule "Prelude"
mod_PreludeList  = plainModule "PreludeList"
mod_PreludeText  = plainModule "PreludeText"
mod_Ix	   = plainModule "Ix"
--}

{-
-- For use with Hugs libraries:
mod_Prelude      = plainModule "Hugs.Prelude"
mod_PreludeList  = mod_Prelude
mod_PreludeText  = mod_Prelude
mod_Ix		 = mod_Prelude
--}

--------------------------------------------------------------------------------

--prelude_mod         = mod_Prelude -- retained for backward compatibility

main_mod path       = moduleName path "Main"

--qualify path m v         = Qual (moduleName path m) v
tuple n            = "(" ++ replicate n ',' ++ ")"        

unit_con_name       = Qual mod_Prelude "()"
tuple_con_name n    = Qual mod_Prelude $ tuple n

main_name           = UnQual "main"

unit_tycon_name     = unit_con_name

instance HasSpecialNames HsName where
  fun_tycon_name      = Qual mod_Prelude "->"
  list_tycon_name     = Qual mod_Prelude "[]"
  char_tycon_name     = Qual mod_Prelude "Char"
  tuple_tycon_name n  = tuple_con_name n

 
instance IsSpecialName HsName where
  is_list_tycon_name  = std_is_list_tycon_name
  is_fun_tycon_name   = std_is_fun_tycon_name
  is_char_tycon_name  = std_is_char_tycon_name
  is_tuple_tycon_name = std_is_tuple_tycon_name

is_unit_tycon_name n = n==unit_tycon_name
