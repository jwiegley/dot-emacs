-- Refactored type inference for the E structure.
-- Returns types and translated expressions.
module TiE where
import HasBaseStruct
import BaseSyntaxStruct
import SrcLoc1
import TI
import TiLit(tcLit)
import TiFields
import TiRhs
--import TiPrelude
import MUtils
import Control.Monad(join)--,liftM2

instance HasId i (EI i e p ds t c) where
  ident = HsId
  isId (HsId x) = Just x
  isId _ = Nothing

instance (HasBaseStruct e (EI i e p ds t c),HasId i p) => HasAbstr i (EI i e p ds t c) where
  abstract xs e = HsLambda (map var xs) (base e)

{-+
When inferring the type of an expression, we return a type and a transformed
expression, which can be of any (extended) expression type, hence the
requirement HasCoreSyntax e, HasBaseStruct e ... and the result type Typed e.
-}
{-
-- Copied from the type inferred for tcE by GHC:
instance (Fresh i,TypeId i,ValueId i,
	  HasSrcLoc i, -- for error reporting
	  HasBaseStruct rec (EI i e x r t1 c1),
	  HasTypeAnnot i e,HasTypeAnnot i x,
	  TypeCheck i p1 (Typed i x),
	  TypeCheck i e1 (Typed i e),
	  TypeCheckDecls i ds r,
	  HasBaseStruct e1 (EI i e1 p1 ds t2 c2), HasId i p1, HasAbstr i e1,
	  HasBaseStruct p1 (PI i p), HasCoreSyntax i e1, HasTypeApp i rec,
	  HasLit rec,HasTypeAnnot i rec,
	  DefinedNames i p1, TypeCheck i e1 (Typed i rec),
	  HasBaseStruct d1 (DI i e1 p2 ds1 t c tp),
	  HasId i p2, HasDef ds1 d, HasDef ds d1)
 => TypeCheck i (EI i e1 p1 ds t c) (Typed i rec)
  where tc = tcE
-}
tcE e =
  case e of
    HsId n                 -> inst_loc n
    HsLit s l              -> tcLit (hsLit s) s l
    HsInfixApp x op z      -> inst_loc op `tapp` tc x `tapp` tc z
    HsApp x y              -> tc x `tapp` tc y
    HsNegApp s x           -> instPrel_srcloc s "negate" `tapp` tc x
    HsLambda ps e          -> tcLambda ps e
    HsLet ds e             -> tcLet ds (tc e)
    HsIf x y z             -> join $ tcIf # tc x <# tc y <# tc z
    HsCase e alts          -> tcCase e alts
    HsDo stmts             -> tcStmts stmts
    HsTuple es             -> typedTuple =<< mapM tc es
    HsList es              -> tcList =<< mapM tc es
    HsParen e              -> emap hsParen # tc e
    HsLeftSection x op     -> inst_loc op `tapp` tc x
    HsRightSection op y    -> instPrel "flip" `tapp` inst_loc op `tapp` tc y
    HsRecConstr s c fields -> tcFieldsCon s c fields
    HsRecUpdate s e upds   -> tcFieldsUpd s (tc e) upds
    HsEnumFrom x           -> instPrel "enumFrom" `tapp` tc x
    HsEnumFromTo x y       -> instPrel "enumFromTo" `tapp` tc x `tapp` tc y
    HsEnumFromThen x y     -> instPrel "enumFromThen" `tapp` tc x `tapp` tc y
    HsEnumFromThenTo x y z ->
      instPrel "enumFromThenTo" `tapp` tc x `tapp` tc y `tapp` tc z
    HsListComp stmts       -> emap hsListComp # tcLComp stmts
    HsExpTypeSig s e c t    -> tcExpTypeSig s e c t
    _ -> fail "Bug: not implemented yet"

tcLambda ps e =
  do (ps',e'):>:(tps,t') <- tcLambda' ps e
     let tps' = zipWith typeAnnot ps' tps
     hsLambda tps' (typeAnnot e' t') >: foldr hsTyFun t' tps

tcLambda' ps e =
  do bs <- schintro (patternVars ps)
     extendts bs $ do ps':>:tps <- unzipTyped # mapM tc ps
                      e':>:t'   <- tc e
                      (ps', e') >: (tps,t')

tcDsLambda' ps ds e =
  do bs <- schintro (patternVars ps)
     extendts bs $ do ps':>:tps <- unzipTyped # mapM tc ps
                      ds':>:dbs <- tcLocalDecls ds
                      e':>:t'   <- extendts dbs (tc e)
		      --let ds'' = addDeclsType ([],bs) ds'
                      (ps', ds', e') >: foldr hsTyFun t' tps

tcLet ds tce =
  do ds':>: bs <- tcLocalDecls ds
     e' :>: t' <- extendts bs tce
     hsLet ds' e' >: t'

tcExpTypeSig s e c t =
 do v <- fresh
    tc (hsLet (hsTypeSig s [v] c t `consDef`
	       (hsPatBind s (var v) (HsBody e) noDef `consDef` noDef))
	      (var v)  `asTypeOf` e)
    
--tcIf :: HasBaseStruct e (E e p ds t c) => Typed e -> Typed e -> Typed e -> TI (Typed e)
tcIf (cnd:>:tcnd) (thn:>:tthn) (els:>:tels) =
  do tBool <- getBoolType
     tcnd=:=tBool
     tthn=:=tels
     hsIf cnd thn els >:: tthn

tcCase e alts =
  do e':>:te <- tc e
     alts':>:ats <- unzipTyped # mapM tcAlt alts
     let (tps,tes) = unzip ats
     mapM_ (te=:=) tps
     t <- allSame tes
     hsCase e' alts' >:: t

e >:: t = typeAnnot e t >: t

tcAlt (HsAlt s p rhs ds) = 
  do bs <- schintro (patternVars p)
     extendts bs $ do p':>:tp <- tc p
	              ds':>:dbs <- tcLocalDecls ds
	              rhs':>:trhs <- extendts dbs (tc rhs)
		      --let ds'' = addDeclsType ([],bs) ds'
                      HsAlt s p' rhs' ds'>:(tp,trhs)
     
tcStmts stmts =
  do bind <- ident # prelValue ">>="
     thn <- ident # prelValue ">>"
     fail <- ident # prelValue "fail"
     let desugar stmt =
	   case stmt of
	     HsGenerator _ p e stmt -> app (bind `app` e) # match p stmt
	     HsQualifier   e stmt -> app (thn `app` e) # desugar stmt
	     HsLetStmt    ds stmt -> hsLet ds # desugar stmt
	     HsLast        e      -> return e
	 match p stmt =
	   do stmt' <- desugar stmt
	      case isVar p of
		Just v -> return $ abstract [v] stmt'
		_ -> do v <- fresh
			return (abstract [v] $
				 hsCase (var v) [p -+> stmt',
						 hsPWildCard -+> hsFailInDo])
	 hsFailInDo =
           fail `app` hsLit loc0 (HsString "pattern match failure in do")
	 p -+> e = HsAlt loc0 p (HsBody e) noDef
     tc =<< desugar stmts

tcLComp lc =
  case lc of
    HsGenerator s p e lc -> do e':>:et <- tc e
			       bs <- schintro (patternVars p)
			       let ext = extendts bs
			       p':>:pt <- ext (tc p)
			       listType <- getListType
			       et=:=listType pt
			       emap (HsGenerator s p' e') # ext (tcLComp lc)
    HsQualifier e   lc -> do e':>:t <- tc e
			     tBool <- getBoolType
			     t=:=tBool
			     emap (HsQualifier e') # tcLComp lc
    HsLetStmt    ds lc -> do ds':>: bs <- tcLocalDecls ds
			     emap (HsLetStmt ds') # extendts bs (tcLComp lc)
    HsLast      e      -> do e':>:t <- tc e
			     listType <- getListType
		             HsLast e' >: listType t
