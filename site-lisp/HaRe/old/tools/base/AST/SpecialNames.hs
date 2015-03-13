module SpecialNames where

class HasSpecialNames i where
  list_tycon_name,fun_tycon_name,char_tycon_name :: i -- "[]", "(->)", "Char"
  tuple_tycon_name :: Int-> i -- tuple_tycon_name 2 = "(,,)"

  tuple_name          :: Int -> i

  -- a bit of a hack...
  tuple_name          = tuple_tycon_name


class Eq i => IsSpecialName i where
  is_list_tycon_name, is_fun_tycon_name, is_char_tycon_name :: i->Bool
  is_tuple_tycon_name :: Int->i->Bool

  is_tuple_name     :: Int -> i -> Bool
  is_tuple_name     = is_tuple_tycon_name


std_is_list_tycon_name i      = i==list_tycon_name
std_is_fun_tycon_name i       = i==fun_tycon_name
std_is_char_tycon_name i      = i==char_tycon_name
std_is_tuple_tycon_name n i   = i==tuple_tycon_name n

std_is_tuple_name n i         = i==tuple_name n
