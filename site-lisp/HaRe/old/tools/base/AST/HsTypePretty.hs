{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE UndecidableInstances  #-}
--- Pretty printing for the T functor ------------------------------------------

module HsTypePretty where

import HsTypeStruct
--import HsIdent
import PrettySymbols(rarrow,forall')
import PrettyPrint
import PrettyUtil

instance (Printable i,Printable t,PrintableApp t t) => Printable (TI i t) where
    ppi (HsTyFun a b)     = sep [ wrap a <+> rarrow, ppi b ]
    ppi (HsTyApp f x)     = ppiApp f [x]
    ppi (HsTyForall xs ts t) = forall' <+> hsep (map ppi xs) <> kw '.' <+> ppContext ts <+> t
    ppi t                 = wrap t

--  wrap (HsTyTuple ts)   = ppiTuple ts
    wrap (HsTyApp f x)    = wrapApp f [x]
    wrap (HsTyVar v)      = wrap v
    wrap (HsTyCon c)      = tcon (wrap c)
    wrap t                = parens $ ppi t

instance (PrintableApp i t,PrintableApp t t) => PrintableApp (TI i t) t where
  ppiApp (HsTyApp tf ta) ts = ppiApp tf (ta:ts)
  ppiApp (HsTyCon c)     ts = ppiApp c ts
  ppiApp t               ts = wrap t<+>fsep (map wrap ts)

  wrapApp (HsTyApp tf ta) ts = wrapApp tf (ta:ts)
  wrapApp (HsTyCon c)     ts = wrapApp c ts
  wrapApp t               ts = parens (wrap t<+>fsep (map wrap ts))
