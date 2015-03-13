{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
module SourceNames where
import HsName(Id,HsName(..),hsUnQual,ModuleName(..),moduleName)
import SrcLoc1(SrcLoc,loc0,srcFile)
import qualified SrcLoc1 as L
import PrettyPrint
import HasBaseName
import UniqueNames
import QualNames
import SpecialNames

import Data.Char(isUpper)

import Data.Generics

data SN i = SN i SrcLoc deriving (Data, Typeable)

instance Show i => Show (SN i) where
  showsPrec p (SN i _) = showsPrec p i

instance Read i => Read (SN i) where
  readsPrec p s = [(SN i loc0,r)|(i,r)<-readsPrec p s]

instance Unique (SN HsName) where
  unique m (SN n p) = G m (hsUnQual n) (srcLoc p)

instance Unique (SN Id) where
  unique m (SN n p) = G m n (srcLoc p)

--srcName (PN n _) = SN n loc0 -- a temporary hack (I hope)
srcName n = SN (getBaseName n) (L.srcLoc n)
fakeSN n = SN n loc0

instance HasBaseName (SN i) i where getBaseName (SN i _) = i

instance Eq i  => Eq  (SN i) where SN n1 _==SN n2 _ = n1==n2
instance Ord i => Ord (SN i) where compare (SN n1 _) (SN n2 _) = compare n1 n2

instance Functor SN where fmap f (SN i o) = SN (f i) o

instance QualNames qn m n => QualNames (SN qn) m (SN n) where
    getQualifier                = getQualifier . getBaseName
    getQualified                = fmap getQualified

    mkUnqual                    = fmap mkUnqual
    mkQual m                    = fmap (mkQual m)

instance HasSpecialNames i => HasSpecialNames (SrcLoc->SN i) where
  list_tycon_name = SN list_tycon_name
  fun_tycon_name = SN fun_tycon_name
  char_tycon_name = SN char_tycon_name
  tuple_tycon_name = SN . tuple_tycon_name

instance IsSpecialName i => IsSpecialName (SN i) where
  is_list_tycon_name (SN i _) = is_list_tycon_name i
  is_fun_tycon_name (SN i _) = is_fun_tycon_name i
  is_char_tycon_name (SN i _) = is_char_tycon_name i
  is_tuple_tycon_name n (SN i _) = is_tuple_tycon_name n i

---

instance Printable   i => Printable   (SN i) where
  ppi (SN n p) = ppi n<>ppIfDebug ("<<"<>p<>">>")
  wrap (SN n p) = wrap n<>ppIfDebug ("<<"<>p<>">>")

            -- positions ends up outside parenthesis...

instance PrintableOp i => PrintableOp (SN i) where
  isOp (SN n p) = isOp n
  ppiOp (SN n p) = ppiOp n<>ppIfDebug ("<<"<>p<>">>")


hsName2modName (SN hs loc) =
  case hs of
    UnQual m -> return (SN (moduleName (srcFile loc) m) loc)
    Qual m n@(c:_) ->
	 if isUpper c
         then return (SN (PlainModule (mn m++"."++n)) loc)
         else fail "Invalid hierarchical module name"
       where mn (PlainModule s) = s
             mn (MainModule _) = "Main"
