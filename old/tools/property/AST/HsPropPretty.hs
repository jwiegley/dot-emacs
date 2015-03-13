module HsPropPretty where
import HsPropStruct
import PrettyPrint
import PrettySymbols as S
import HsIdentPretty()

--delta = kwIfUnicode '\x0394' "$"
delta = "$"

instance Printable Quantifier where
  ppi All = S.all
  ppi Exist = exist

instance (Printable i,Printable pa,Printable pp) => Printable (PD i pa pp) where
  wrap = ppi
  ppi pd =
    case pd of
      HsPropDecl s n ns p -> sep [kw "property" <+> n <+> fsep ns <+> equals,
				  funNest p]
      HsAssertion s optn a -> sep [kw "assert" <+> maybe empty (<+>equals) optn,
                                   funNest a]

instance (Printable i,Printable e,Printable t,Printable pa,Printable pp)
       => Printable (PA i e t pa pp) where
  wrap pa =
    case pa of
      PropApp i _ [] -> wrap i
      PropParen p -> parens p
      _ -> parens pa

  ppi pa =
    case pa of
      Quant q i optt pa -> sep [q <+> i <+> ppOptType optt <+> kw ".", ppi pa]
      --PropId i -> ppi i
      PropApp i ts [] -> wrap i
      PropApp i ts ps -> wrap i <+> fsep (map ppPredArg ps)
      PropNeg a -> S.not <+> a		   
      PropOp op a1 a2 -> ppiBinOp (wrap a1) (ppOp op) (wrap a2)
      PropEqual e1 e2 -> ppiBinOp (braces e1) (kw "===") (braces e2)
      PropHas e p -> ppiBinOp (braces e) (kw ":::") (ppi p)
      PropParen p -> parens p
--    PropLambda i pa -> lambda<+>i<+>rarrow<+>pa
--    PropLet i optt e pa -> sep ["let"<+>i<+>ppOptType optt<+>"="<+>e,
--				  "in"<+>pa]

instance Printable PropOp where ppi = ppOp

ppOp op =
  ppi $ case op of
	  Conj  -> S.and
	  Disj  -> S.or
	  Imp   -> implies
	  Equiv -> equiv

instance (PrintableOp i,Printable e,Printable p,Printable t,Printable pa,Printable pp)
       => Printable (PP i e p t pa pp) where
  wrap pp =
    case pp of
      PredApp i _ [] -> wrap i
      PredNil -> kw "[]"
      PredLifted e -> kw "!"<>braces e
      PredStrong p -> delta<>wrap p
      PredParen p -> parens p
      PredComp pts a -> kw "{|"<+>ppiFSeq (map ppts pts)<+>kw "|"<+>a<+>kw "|}"
        where ppts (p,optt) = p<+>ppOptType optt
      _ -> parens pp

  ppi pp =
    case pp of
      PredApp i ts [] -> wrap i
      PredApp i ts ps -> wrap i <+> fsep (ppPredArgs ps)
      PredArrow p1 p2 -> ppiBinOp (wrap p1) rarrow (wrap p2)
      PredInfixApp p1 i p2 -> ppiBinOp (wrap p1) (ppiOp i) (wrap p2)
      PredNeg optt p -> S.not <+> p
      PredOp op optt p1 p2 -> ppiBinOp (wrap p1) (ppOp op) (wrap p2)
      PredLfp i optt p -> mu <+> i <+> ppOptType optt <+> kw "." <+> p
      PredGfp i optt p -> nu <+> i <+> ppOptType optt <+> kw "." <+> p
      _ -> wrap pp

ppPredArgs as = map ppPredArg as
ppPredArg a = either braces wrap a

ppOptType x = maybe empty (el<+>) x
