{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module SyntaxRecPretty where
import SyntaxRec
import PrettyPrint
import SpecialNames
import HsTypeStruct
import PrettySymbols(rarrow)

instance (PrintableOp i,IsSpecialName i) => Printable (HsDeclI i) where
    ppi (Dec d) = ppi d

    ppiList []  = empty
    ppiList ds  = vcat $ (map (blankline . ppi) (init ds)) ++ [ppi (last ds)]

    wrap (Dec d) = wrap d


{- We want something like this,

   instance Rec rec struct => Printable rec where
     ppi = ppi . struct
     wrap = ppi . struct

   but we have to repeat it for each type in the Rec class, since otherwise
   we get an instance that "overlaps" with everything else... /TH
-}

instance (PrintableOp i,IsSpecialName i) => Printable (HsExpI i) where
    ppi = ppi . struct
    wrap = wrap . struct

instance PrintableOp i => Printable (HsPatI i) where
    ppi = ppi . struct
    wrap = wrap . struct

instance (Printable i,IsSpecialName i) => Printable (HsTypeI i) where
    --ppi (Typ (HsTyApp (Typ (HsTyCon (Qual (Module "Prelude") "[]"))) t)) =
    --    brackets $ appParensOff $ ppi t
    ppi (Typ t) = ppi t

--  ppiList [] = empty
--  ppiList ts = {-appParensOn $-} ppiSet space $ map struct ts

    --wrap (Typ (HsTyApp (Typ (HsTyCon (Qual (Module "Prelude") "[]"))) t)) =
    --	brackets $ appParensOff $ ppi t
    wrap (Typ t) = wrap t

instance (Printable i,IsSpecialName i) => PrintableApp (HsTypeI i) (HsTypeI i) where
   ppiApp = ppiApp . struct
   wrapApp = wrapApp . struct

instance Printable HsKind where
    ppi = ppi . struct
    wrap = wrap . struct


instance (Printable i,IsSpecialName i) => PrintableApp i (HsTypeI i) where
  ppiApp i ts = -- i is always a  constructor, not a type variable
      case ts of
        [t]     | is_list_tycon_name i -> ppListType t
        [t1,t2] | is_fun_tycon_name  i -> sep [wrap t1<+>rarrow,ppi t2]
        _       | n>=2 && is_tuple_tycon_name (n-1) i -> ppiFTuple ts
	_                              -> tcon (wrap i)<+>fsep (map wrap ts)
    where
      n=length ts

  wrapApp i ts =
      case ts of
        [t]     | is_list_tycon_name i -> ppListType t
        [t1,t2] | is_fun_tycon_name  i -> parens (sep [wrap t1<+>rarrow,ppi t2])
        _       | n>=2 && is_tuple_tycon_name (n-1) i -> ppiFTuple ts
	_                         -> parens (tcon (wrap i)<+>fsep (map wrap ts))
    where
      n=length ts

ppListType t =
  case t of
    Typ (HsTyCon i) | is_char_tycon_name i -> tcon "String"
    _ -> brackets t
