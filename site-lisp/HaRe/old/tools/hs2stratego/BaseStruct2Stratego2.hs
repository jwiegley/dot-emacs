{-+
Reusable functions for translation from the (non-recursive) base structure
to Stratego.
-}

module BaseStruct2Stratego2 where
import StrategoAST2
import BaseSyntax -- non-recursive base syntax structure
import PrettyPrint(pp)
import UniqueNames(orig,Orig(G))
import TypedIds(IdTy(..),idTy)
import TiDefinedNames(definedTypeName)
import DefinedNames(contextSize)
import TiNames(superName)
import Parentheses

transId x = 
  case orig x of
    G m n _ -> pp m++"."++pp n
    _ -> pp x

transL lit =
  case lit of
    HsInt   i  -> hInt i
    HsChar  c  -> hChar [c]
    HsString s -> hString s -- desugar into list of characters?
    HsFrac   x -> hFrac x

transPId i =
  case i of
    HsVar x -> varPat x
    HsCon c -> ConstrPat (c,[])

transP trId trP p =
 case mapPI trId trP p of
   HsPId i -> transPId i
   HsPLit _ lit -> litPat (transL lit) -- new
{- old
   HsPLit _ (HsInt _ i) -> litPat i
   HsPLit _ (HsChar c) -> charLitPat c
   HsPLit _ (HsString s) -> stringLitPat s
-- other literals...
-}
-- HsPSucc _ n l -> ...
   HsPInfixApp x op y -> ConstrPat (op,[x,y])
   HsPApp c ps -> ConstrPat (c,ps)
   HsPTuple s ps -> tuplePat ps
   HsPList s ps -> plist ps
   HsPParen p -> p
-- HsPRec
   HsPAsPat x p -> AsPattern (x,p)
   HsPWildCard -> WildCard
   HsPIrrPat p -> twiddlePat p
   _ -> not_supported "Pattern" p


transD trId trE trP trDs trT trC trTp d =
 case d of
   HsClassDecl loc c tp fd ds -> defs (transClassDecl tp)
   HsInstDecl loc (Just n) c t ds -> onedef (transInstDecl n c t ds) 
   _ ->
     case mapDI trId trE trP trDs trT trC trTp d of
       HsPatBind loc p rhs ds -> onedef (HDef (p, hlet ds (transRhs rhs)))
       HsFunBind _ [HsMatch _ f ps rhs ds] ->
		onedef (HDef (varPat f,habs ps (hlet ds (transRhs rhs))))
       HsTypeDecl loc tp t -> onedef (tSyn tp t)
       HsDataDecl loc c tp cons ds -> onedef (tData tp (map transCon cons))
       HsNewTypeDecl loc c tp con ds -> onedef (tNew tp (transCon con))
       _ -> [ignored (pp d)]
  where
    onedef d = [def d]
    defs = map def

    transRhs (HsBody e) = e
    transRhs (HsGuard triples) = foldr guard nomatch triples
      where
        guard (loc,guard,body) therest = HIte(guard,body,therest)

    transCon con =
      case con of
        HsConDecl loc _ _ c args -> dCons c (map transConArg args)
        HsRecDecl loc _ _ c args ->
            dCons c [a'|(fs,a)<-args,let a'=transConArg a,f<-fs]

    transConArg arg =
      case arg of
        HsBangedType t -> (Strict,t)
	HsUnBangedType t -> (Lazy,t)

    {-+ Classes are translated to tuple types. The methods are translated
        to tuple field selector functions. -}
    transClassDecl tp =
      case idTy cn of
        Class cnt ms ->
	    [selector i (superName cn (i+1)) | i<-[0..cnt-1]] ++
            zipWith selector [cnt..] ms
	  where
	    arity = cnt+length ms
	    selector i m = HDef (varPat m',habs1 (tpat i) ze)
	      where
		m' = transId m
		tpat i = tuplePat [pick j|j<-[0..arity-1]]
		  where pick j = if j==i then zp else WildCard
       where
         cn = definedTypeName tp

    {-+ Instances are translated into tuple definitons... -}	
    transInstDecl n ctx inst ds =
      case idTy cn of
        Class cnt ms ->
            HDef (varPat n',
		  habs (map varPat dicts) (hTuple (map findDef ms')))
	  where
	    ms' = map (transId . superName cn) [1..cnt]++map transId ms
	    ds' = trDs ds
	    arity = cnt+length ms
	    n' = transId n
	    dicts = ["d"++show i|i<-[1..contextSize ctx]]

            findDef m =
	      case [ e | (HDef (VarPat (P m'),e))<-ds',m'==m] of
	        [e] -> foldl happ e (map hVar dicts)
       where
         cn = definedTypeName inst

transEId i =
  case i of
    HsVar x -> hVar x
    HsCon c -> HCon (c,[])

transE trId trE trP trDs trT trC e =
 case mapEI trId trE trP trDs trT trC e of 
   HsId i                      -> transEId i
   HsApp x y                   -> x `happ` y
   HsLit _ lit                 -> hLit (transL lit) -- new
{- old
   HsLit _ (HsInt _ i)         -> hLit i
   HsLit _ (HsChar c)          -> hCharLit c
   HsLit _ (HsString s)        -> hStringLit s
-}
-- other literals...
   HsInfixApp x (HsVar op) z   -> hVar op `happ` x `happ` z
   HsInfixApp x (HsCon c) z    -> HCon (c,[x,z]) -- !! constructor arity?
   HsNegApp _ x                -> hVar "Prelude.negate" `happ` x
   HsLambda ps e               -> habs ps e
   HsLet ds e                  -> hlet ds e
   HsIf x y z                  -> HIte (x, y, z)
   HsCase e alts               -> HCase (e,map transAlt alts)
   HsTuple xs                  -> hTuple xs
   HsList xs                   -> hlist xs
   HsParen x                   -> x
   HsLeftSection x (HsVar op)  -> hleftsection x op 
   HsRightSection (HsVar op) y -> hrightsection op y
   HsLeftSection x (HsCon c)   -> hconleftsection x c
   HsRightSection (HsCon c) y  -> hconrightsection c y
   -- The following removed by the type checker too...
   HsEnumFrom e1	       -> hVar "Prelude.enumFrom" `happ` e1
   HsEnumFromTo e1 e2	       -> hVar "Prelude.enumFromTo" `happ` e1 `happ` e2
   HsEnumFromThen e1 e2	       ->
       hVar "Prelude.enumFromThen" `happ` e1 `happ` e2
   HsEnumFromThenTo e1 e2 e3   ->
       hVar "Prelude.enumFromThenTo" `happ` e1 `happ` e2 `happ` e3
   HsExpTypeSig _ e c t        -> e -- !!
   _ -> hVar (not_supported_msg "Expression" e) -- !!
  where
    transAlt alt =
      case alt of
	 HsAlt loc pat rhs _ -> HBranch (pat,transRhs rhs) -- !!!
	 --_ -> not_supported "Case branch" "'where' clauses"
      where
	transRhs (HsBody e)       = [nonGuarded e]
	transRhs (HsGuard gdrhss) = [Guarded (g,e)|(_,g,e)<-gdrhss]


transT trId trT t =
  case mapTI trId trT t of
    HsTyFun t1 t2 -> TArrow (t1,t2)
    HsTyApp t1 t2 -> tApp t1 t2
    HsTyVar a -> tVar a
    HsTyCon c -> tConst c
    _ -> not_supported "Type" t

transTp trId trTp trTa t =
  case t of
    HsTyApp t1 t2 -> (c,vs++[trTa t2])
      where (c,vs) = trTp t1
    HsTyCon c -> (trId c,[])
    _ -> not_supported "LHS in type decl" t

transTa trId t =
  case t of
    HsTyVar a -> trId a
    _ -> not_supported "Type parameter in LHS of type decl" t

not_supported s x = error $ not_supported_msg s x
not_supported_msg s x = s++" not supported (yet): "++pp x
