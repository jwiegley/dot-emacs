module HsModulePretty where
import HsModule
import HsIdentPretty
import PrettyPrint

instance (Printable m,Printable i,Printable ds)
       => Printable (HsModuleI m i ds) where
    ppi (HsModule s mod exps imps ds) =
	sep [kw "module" <+> modn mod,
	     classNest $ sep [ maybepp ppiFTuple exps, kw "where" ]]
	$$ layout (map ppi imps++map (blankline$) (ppis ds))

	where vspace :: [Doc] -> Doc
	      vspace [] = empty
	      vspace ds = blankline $ vcat ds

instance (Printable m,Printable i) => Printable (HsExportSpecI m i) where
    ppi (EntE e) = ppi e
    ppi (ModuleE m) = kw "module" <+> modn m

instance (Printable m,Printable i) => Printable (HsImportDeclI m i) where
    ppi (HsImportDecl _ m qual m' imps) =
	kw "import" <+> optpp qual (kw "qualified") <+> modn m <+>
        maybepp ((kw "as"<+>).modn) m' <+> maybepp ppImps imps
      where
        ppImps (hiding, imps) = optpp hiding (kw "hiding") <+> ppiFTuple imps

instance Printable i => Printable (EntSpec i) where
    ppi (Var n)         = wrap n
    ppi (Abs n)         = tcon n -- could be a predicate in the P-logic ext
    ppi (AllSubs m)     = tcon m <> "(..)"
    ppi (ListSubs m ns) = tcon m <> ppiFTuple (map (ppcon wrap) ns)
