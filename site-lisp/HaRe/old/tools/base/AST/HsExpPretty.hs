-- Pretty printing for the E functor.

module HsExpPretty () where

import HsExpStruct
import HsGuardsPretty()
import HsFieldsPretty()
import HsLiteralPretty()
import HsExpUtil(getStmtList,HsStmtAtom(..))
import HsDeclPretty(ppContext)
import PrettyPrint
import PrettySymbols(lambda,larrow,rarrow,el)
import HsIdent
import HsIdentPretty

instance (PrintableOp i,Printable e, Printable p, Printable ds, Printable t, Printable c) =>
         Printable (EI i e p ds t c) where
  ppi e =
    case e of
      HsId n                 -> ppcon wrap n
      HsLit s l              -> lit l
      HsInfixApp x op z      -> ppiBinOp (wrap x) (ppconop ppiOp op) (wrap z)
--    HsInfixApp x op z      -> parenBinOp x (ppcon ppiOp op) z -- problem?

      -- if x is a lambda it need parens, but the parser preserves parens!
      HsApp x y              -> sep [ ppi x, letNest (wrap y) ]
      HsNegApp s x           -> '-' <> x
      HsLambda ps e          -> sep [ lambda <+> sep (map wrap ps) <+>
					rarrow, letNest e ]
      HsLet ds e             -> sep [kw "let" <+> ds, kw "in" <+> letNest e]
      HsIf x y z             -> sep [kw "if" <+> x,
				     doElseNest (kw "then"<+>y),
				     doElseNest (kw "else"<+>z)]
      HsCase e alts          -> kw "case" <+>  e <+> kw "of"
				 $$ (caseNest $ layout alts)
      HsDo stmts             -> kw "do" <+> (doNotation $ ppi stmts)
      HsTuple xs             -> ppiFTuple xs
      HsList xs              -> ppiList xs
      HsParen x              -> wrap x
      HsLeftSection x op     -> parens $ x <+> ppcon ppiOp op
      HsRightSection op y    -> parens $ ppcon ppiOp op <+> y
--    HsRecConstr s n []     -> ppi n -- "A {}" is NOT the same as "A"!!
      HsRecConstr s n upds   -> con n <+> braces upds
      HsRecUpdate s e []     -> ppi e -- never happens with expressions
				       -- that pass static analysis
      HsRecUpdate s e upds   -> e <+> braces upds
      HsEnumFrom x           -> brackets $ x <+> kw ".."
      HsEnumFromTo x y       -> brackets $ x <+> kw ".." <+> y
      HsEnumFromThen x y     -> brackets $ x <> comma <+> y <+> kw ".."
      HsEnumFromThenTo x y z -> brackets $ x <> comma <+> y <+> kw ".." <+> z
      HsListComp stmts       -> ppiListComp $ map ppi $ getStmtList stmts
	where
	  ppiListComp es =
            brackets $ last es <+> '|' <+> (fsep $ punctuate comma (init es))
      HsExpTypeSig s e c t   -> e <+> kw el <+> (ppContext $ ppis c) <+> t
      HsAsPat n p            -> n <+> kw '@' <+> wrap p
      HsWildCard             -> kw '_'
      HsIrrPat p             -> kw '~' <> wrap p

  wrap e =
    case e of
      HsId n                -> ppcon wrap n
      HsLit s l             -> lit l
      HsTuple xs            -> ppi e
      HsList xs             -> ppi e
      HsParen x             -> wrap x
      HsLeftSection x op    -> ppi e
      HsRightSection op y   -> ppi e
      HsRecConstr s n _     -> ppi e
      HsRecUpdate s e []    -> wrap e -- never happens with expressions
					 -- that pass static analysis
      HsEnumFrom x          -> ppi e
      HsEnumFromTo x y      -> ppi e
      HsEnumFromThen x y    -> ppi e
      HsEnumFromThenTo x y z-> ppi e
      HsListComp stmts      -> ppi e
      HsAsPat n p           -> ppi e
      HsWildCard            -> kw '_'
      _ -> parens e    

instance (Printable e, Printable p, Printable ds)
         => Printable (HsStmt e p ds) where
    ppi = layout . map ppi . getStmtList
    --ppi = vcat . getStmtList

    wrap (HsLast e) = wrap e
    wrap s          = parens $ ppi s

instance (Printable e, Printable p, Printable ds)
         => Printable (HsStmtAtom e p ds) where
    ppi (HsGeneratorAtom _ p e) = p <+> larrow <+> e
    ppi (HsQualifierAtom e)   = ppi e
    ppi (HsLetStmtAtom ds)    = kw "let" <+> ds
    ppi (HsLastAtom e)        = ppi e

    wrap (HsLastAtom e) = wrap e
    wrap s              = parens s
