module HsDeclPretty (ppContext,ppFunDeps) where

import HsDeclStruct
import HsIdentPretty()
import HsAssocPretty()
import PrettySymbols(el,rarrow)
import PrettyPrint
import PrettyUtil(ppWhere,ppContext)
import HsGuardsPretty(ppRhs)


instance (PrintableOp i,Printable e, Printable p, Printable ds,
	  Printable t, Printable c, Printable tp) =>
         Printable (DI i e p ds t c tp) where
    ppi (HsTypeDecl _ tp t)                  =
        sep [kw "type" <+> tp <+> equals, dataNest t ]
    ppi (HsNewTypeDecl _ c tp t ders)        =
        sep [kw "newtype" <+> (ppContext $ ppis c) <+> tp <+> equals,
	       dataNest $ sep [ppi t, ppDeriving ders] ]
    ppi (HsDataDecl _ c tp summands ders)    =
        sep [kw "data" <+> (ppContext $ ppis c) <+> tp,
               dataNest $ 
	         sep [sep (zipWith (<+>) (equals : repeat (kw "|")) summands),
                      ppDeriving ders]]
    ppi (HsClassDecl _ c tp fundeps ds)               =
        sep [kw "class" <+> sep [ppContext $ ppis c, ppi tp, ppFunDeps fundeps],
             nest 2 $ ppWhere (ppis ds)]
    ppi (HsInstDecl _ optn c tp ds)                =
        sep [kw "instance" <+> sep [ppContext $ ppis c, ppi tp],
	     nest 2 $ ppWhere (ppis ds)]
    ppi (HsDefaultDecl _ t)                   =	kw "default" <+> ppiFTuple t
    ppi (HsTypeSig _ ns c t)                  =
	-- If they are printed vertically, every name except the first one
	-- must be indented...
        sep [hcat (punctuate comma (map wrap ns)),
	     letNest $  el <+> ppContext (ppis c) <+> t]
    ppi (HsFunBind _ ms)                      =  vcat ms
    ppi (HsPatBind _ p rhs ds)                =
        sep [wrap p, nest 2 $ sep [ppRhs equals rhs, ppWhere (ppis ds)]]
    ppi (HsInfixDecl _ fixity ops) =
	fixity <+> (fsep $ punctuate comma $ map ppiOp ops)

    ppi (HsPrimitiveTypeDecl _ ctx tp)       =
        kw "data" <+> ppContext (ppis ctx) <+> tp
    ppi (HsPrimitiveBind _ nm tp)            =
        kw "foreign" <+> kw "import" <+> wrap nm <+> el <+> tp

    wrap = ppi


instance (Printable i,Printable e, Printable p, Printable ds) =>
         Printable (HsMatchI i e p ds) where
    ppi (HsMatch _ f ps rhs ds) 
	= sep [wrap f <+> fsep (map wrap ps),
	       nest 2 $ sep [ppRhs equals rhs, ppWhere (ppis ds)]]

    wrap = ppi


instance (PrintableOp i,Printable t,Printable c)
      => Printable (HsConDeclI i t c) where
    ppi (HsConDecl _ is c n [t1,t2]) | isOp n = ppiBinOp t1 (con (ppiOp n)) t2
    ppi (HsConDecl _ is c n ts) = con (wrap n) <+> (fsep $ map wrap ts)
    ppi (HsRecDecl _ is c n fs)
	= con (wrap n) <+> (braces $ ppiFSeq $ map ppField fs)
	  where ppField (ns, t) = wrapFSeq ns <+> el <+> t

    wrap = ppi


instance Printable t => Printable (HsBangType t) where
    ppi (HsBangedType t)   = kw '!' <> wrap t
    ppi (HsUnBangedType t) = ppi t

    wrap (HsBangedType t)   = kw '!' <> wrap t
    wrap (HsUnBangedType t) = wrap t


-- Pretty prints deriving clauses
--ppDeriving :: [HsName] -> Doc
ppDeriving []  = empty
ppDeriving [i] = kw "deriving" <+> tcon i
ppDeriving is  = kw "deriving" <+> ppiFTuple (map tcon is)

ppFunDeps [] = empty
ppFunDeps fs = kw '|' <+> ppiFSeq (map ppFunDep fs)

ppFunDep (ts1,ts2) = fsep ts1<>rarrow<>fsep ts2
