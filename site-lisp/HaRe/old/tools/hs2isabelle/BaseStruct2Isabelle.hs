{-+
Reusable functions for translation from the (non-recursive) base structure
to Isabelle.
-}

module BaseStruct2Isabelle where
import IsabelleAST
import BaseSyntax -- non-recursive base syntax structure
import PrettyPrint(pp)
import PropSyntaxStruct(Q((:=>)))
import Char(isAlpha)

-- translate identifiers
transId x = pp x
{-
transId x = 
  case orig x of
    G m n _ -> pp m++"."++pp n
    _ -> pp x
-}

-- translate literals
transL lit =
  case lit of
    HsInt   i  -> HInt i
    HsChar  c  -> not_supported "character literal" lit
    HsString s -> not_supported "string literal" lit
    HsFrac   x -> not_supported "fraction literal" lit

-- translate patterns
transP trId trP p =
  case mapPI trId trP p of
    HsPId (HsVar x) -> HVar x
    HsPId (HsCon c) -> HVar c
    HsPLit _ lit -> transL lit -- new
--  HsPSucc _ n l -> ...
    HsPInfixApp x op y -> HInfix x op y
    HsPApp c ps -> hApps (HVar c) ps
    HsPTuple s ps -> HTuple ps
    HsPList s ps -> HList ps
    HsPParen p -> p
--  HsPRec
    HsPAsPat _ _ -> not_supported "as-pattern" p
    HsPWildCard -> HVar "dummy" -- not_supported "wildcard pattern" p
    HsPIrrPat _ -> not_supported "irrefutable pattern" p
    _ -> not_supported "Pattern" p

-- translate declarations
transD trId trE trP trDs trT trC trTp d =
  case mapDI trId trE trP trDs trT trC trTp d of
    HsPatBind _ p rhs ds ->
      IsaFixrec (FixrecDecl [HMatches [HMatch p (transRhs rhs)]])
    HsFunBind _ ms ->
      IsaFixrec (FixrecDecl [HMatches (map transMatch ms)])
    HsTypeDecl _ tp t ->
      IsaTypes (TypesDecl tp t)
    HsDataDecl _ c tp cons ds ->
      IsaDomain (DomainDecl [DomainType tp (map transCon cons)])
    HsNewTypeDecl _ c tp con ds ->
      IsaDomain (DomainDecl [DomainType tp [transCon con]])
    {-
    HsClassDecl SrcLoc c tp (HsFunDeps i) ds |
    HsInstDecl SrcLoc (Maybe i) c t ds |
    HsDefaultDecl SrcLoc [t] |
    HsTypeSig SrcLoc [i] c t |
    HsInfixDecl SrcLoc HsFixity [HsIdentI i] |
    HsPrimitiveTypeDecl SrcLoc c tp |
    HsPrimitiveBind SrcLoc i t
    -}
    _ -> IsaComment (pp d)
  where
    transMatch (HsMatch _ i ps rhs ds) = if isAlpha (head i)
      then HMatch (hApps (HVar i) ps) (transRhs rhs)
      else case ps of [x,y] -> HMatch (HInfix x i y) (transRhs rhs)

    transRhs (HsBody e) = e
    transRhs _ = error "guarded rhs"
    
    transCon con =
      case con of
        HsConDecl loc _ _ c args -> DomainCons c (map transConArg args)
        HsRecDecl loc _ _ c args -> DomainCons c (concatMap transRecArg args)

    transConArg arg =
      case arg of
        HsBangedType t -> DomainArg Strict "" t
        HsUnBangedType t -> DomainArg Lazy "" t
    
    transRecArg (names, arg) =
      case arg of
        HsBangedType t -> [DomainArg Strict n t | n <- names]
        HsUnBangedType t -> [DomainArg Lazy n t | n <- names]


-- translate expressions
transE trId trE trP trDs trT trC e =
  case mapEI trId trE trP trDs trT trC e of 
    HsId (HsVar x)              -> HVar x
    HsId (HsCon c)              -> HVar c
    HsApp x y                   -> HApp x y
    HsLit _ lit                 -> transL lit -- new
    HsInfixApp x (HsVar op) z   -> HInfix x op z
    HsInfixApp x (HsCon c) z    -> HInfix x c z
    -- HsNegApp _ x                -> HVar "Prelude.negate" `HApp` x
    HsLambda ps e               -> hAbss ps e
    -- HsLet ds e                  -> HLet ds e
    HsIf x y z                  -> HIte x y z
    HsCase e alts               -> HCase e (map transAlt alts)
    HsTuple xs                  -> HTuple xs
    HsList xs                   -> HList xs
    HsParen x                   -> x
{-
    HsLeftSection x (HsVar op)  -> hleftsection x op 
    HsRightSection (HsVar op) y -> hrightsection op y
    HsLeftSection x (HsCon c)   -> hConleftsection x c
    HsRightSection (HsCon c) y  -> hConrightsection c y
-}
    -- The following removed by the type checker too...
{-
    HsEnumFrom e1	       -> HVar "Prelude.enumFrom" `HApp` e1
    HsEnumFromTo e1 e2	       -> HVar "Prelude.enumFromTo" `HApp` e1 `HApp` e2
    HsEnumFromThen e1 e2	       ->
       HVar "Prelude.enumFromThen" `HApp` e1 `HApp` e2
    HsEnumFromThenTo e1 e2 e3   ->
       HVar "Prelude.enumFromThenTo" `HApp` e1 `HApp` e2 `HApp` e3
-}
    HsExpTypeSig _ e c t        -> HConstrain e t -- !! what about context?
    _ -> HVar (not_supported_msg "Expression" e) -- !!
  where
    -- translate case alternatives
    transAlt alt =
      case alt of
	HsAlt _ pat (HsBody rhs) _ -> HAlt pat rhs -- !!!
	 --_ -> not_supported "Case branch" "'where' clauses"
      --where
	--transRhs (HsBody e)       = e -- [NonGuarded e]
	--transRhs (HsGuard gdrhss) = undefined -- [Guarded g e|(_,g,e)<-gdrhss]

-- translate types
transT trId trT t =
  case mapTI trId trT t of
    HsTyFun t1 t2 -> TCfun t1 t2
    HsTyApp t1 t2 -> tApp t1 t2
    HsTyVar a -> tVar a
    HsTyCon c -> TType c []
    _ -> not_supported "Type" t

-- translate type declaration LHS
transTp trId trTp trTa t =
  case t of
    HsTyApp t1 t2 -> tApp (trTp t1) (trTa t2)
    HsTyCon c -> TType (trId c) []
    _ -> not_supported "LHS in type decl" t

-- translate type declaration argument LHS
transTa trId t =
  case t of
    HsTyVar a -> tVar (trId a)
    _ -> not_supported "Type parameter in LHS of type decl" t

-- translate qualified types
transQ trC trT (c:=>t) = trT t  -- ignore context for now

not_supported s x = error $ not_supported_msg s x
not_supported_msg s x = s++" not supported (yet): "++pp x
