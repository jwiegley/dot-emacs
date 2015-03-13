{-# OPTIONS -fglasgow-exts #-}
{-# LANGUAGE MultiParamTypeClasses, OverlappingInstances, UndecidableInstances, FunctionalDependencies, NoMonomorphismRestriction #-}
{-+
This module defines instances for the
identifier types #PN# and #PNT# in the classes needed by the type checker.
-}
module TiPNT where
import PNT(PNT(..),PId)
import TiNames
import SrcLoc1(loc0,SrcLoc(..))
import UniqueNames as U
import SpecialNames
import TypedIds
import MUtils
import TiFresh
import HsConstants as Hs(tuple,mod_Prelude)
import QualNames(getQualified)
import TiHsName

instance TypeCon i => TypeCon (PN i) where
  topType m n = PN (topType m n) (G m n noSrcLoc)

instance ValueId i => ValueId (PN i) where
  topName s m n ty = PN (topName s m n ty) (G m n (optSrcLoc s))
  localVal' n Nothing = PN (localVal n) (Sn n loc0) -- hmm
  localVal' n (Just s) = PN (localVal' (n++sh s) (Just s)) (Sn n s)
         where sh (SrcLoc f _ 0 0) = ""
	       sh (SrcLoc f _ r c) = "_"++show r++"_"++show c
--instName m s = PN (instName m s) (I m s)
  dictName' i s = PN (localVal' "d" s) (D i (optSrcLoc s))
  superName (PN n (G m n' s)) k = PN (superName n k) (G m ("super"++show k++"_"++n') s)
  defaultName (PN n (G m n' s)) = PN (defaultName n) (G m (defaultName n') s)

instance TypeVar i => TypeVar (PN i) where
  tvar n = PN (ltvar "t") (D n noSrcLoc)
  ltvar n = PN (ltvar n) P -- just for pretty printing

instance TypeId i => TypeId (PN i)

instance TypeVar i => Fresh (PN i) where
  fresh = tvar # fresh

instance TypeCon PNT where
   topType m n = PNT (topType m n) (Type blankTypeInfo) noSrcLoc

instance ValueId PNT where
  topName s m n ty = PNT (topName s m n ty) ty (optSrcLoc s)
  localVal' n s = PNT (localVal' n s) Value (optSrcLoc s)
--instName m s = PNT (instName m s) Value (U.srcLoc s)
  dictName' i s = PNT (dictName' i s) Value (N s)
  superName (PNT n (Class cnt ms) s) k = PNT (superName n k) (MethodOf (getQualified n) cnt ms) s
  defaultName (PNT n _ s) = PNT (defaultName n) Value s

instance TypeVar PNT where
   tvar n = PNT (tvar n) (Type blankTypeInfo) noSrcLoc
   ltvar n = PNT (ltvar n) (Type blankTypeInfo) noSrcLoc

instance Fresh PNT where fresh = tvar # fresh
instance TypeId PNT

instance TypedId PId PNT where
  idName (PNT n _ _) = getQualified n

instance IsSpecialName i => IsSpecialName (PN i) where
  -- Should probably use the original name instead!
  is_list_tycon_name (PN i _) = is_list_tycon_name i
  is_fun_tycon_name (PN i _) = is_fun_tycon_name i
  is_char_tycon_name (PN _ (G m "Char" _)) = m == mod_Prelude
  is_char_tycon_name _ = False
  is_tuple_tycon_name n (PN i _) = is_tuple_tycon_name n i

instance (TypeCon i,HasSpecialNames i) => HasSpecialNames (PN i) where
  list_tycon_name = prelType "[]"
  fun_tycon_name = prelType "->"
  char_tycon_name = prelType "Char"
  tuple_tycon_name = prelType . Hs.tuple

instance IsSpecialName PNT where
  is_list_tycon_name (PNT i _ _) = is_list_tycon_name i
  is_fun_tycon_name (PNT i _ _) = is_fun_tycon_name i
  is_char_tycon_name (PNT i _ _) = is_char_tycon_name i
  is_tuple_tycon_name n (PNT i _ _) = is_tuple_tycon_name n i

instance HasSpecialNames PNT where
  list_tycon_name = prelType "[]"
  fun_tycon_name = prelType "->"
  char_tycon_name = prelType "Char"
  tuple_tycon_name = prelType . Hs.tuple
