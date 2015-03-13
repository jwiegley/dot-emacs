--Type checking base language declarations (the D structure)
module TiD where
import Data.Maybe(isJust)
import Control.Monad(unless)

import HsDeclStruct
import HsDeclUtil(unbang)
import SrcLoc1(srcLoc)
import HasBaseStruct
import TI hiding (Subst)
import TiDkc
--import TiDinst(tcSelFns)
import TiE(tcDsLambda')
import TiClassInst -- preserves class and instance declarations
--import TiClassInst2(tcInstDecl) -- translates class and instance declarations

--import HsExpStruct(EI)
import HsPatStruct(PI)
import HsIdent(mapHsIdent2)

import MUtils(apFst,( # ))
import SimpleGraphs(reachable')
import PrettyPrint(Printable,pp)

-- For debugging only:
--import IOExts(trace)
--mtrace s = trace s $ done


mapVars f = map $ emap $ mapHsIdent2 f id

instance (TypeVar i,ValueId i,DefinedNames i p,HasId i p,DeclInfo i ds)
         => DeclInfo i (Dinst i e p ds) where
  isUnrestricted expl d =
      case d of
	HsPatBind s p rhs ds -> expl && isJust (isVar p)
	_ -> True
{-
  isTypeDecl d =
      case d of
        HsTypeDecl    {} -> True
        HsNewTypeDecl {} -> True
        HsDataDecl    {} -> True
        HsClassDecl   {} -> True
        HsPrimitiveTypeDecl {} -> True
	_ -> False
-}
  explicitlyTyped kenv tinfo ctx d =
      apFst (map addKind) $
      case d of
	HsTypeDecl s tp t             -> (tiType tp t,[])
	HsNewTypeDecl s ctx tp cd drv -> (tiNewtype ctx tp,
			                  constrTypes ctx tp cd)
	HsDataDecl s ctx tp cds drv   -> (tiData ctx tp,
					  concatMap (constrTypes ctx tp) cds)
	HsClassDecl s c tp fdeps ds   -> (tiClass kenv tinfo c tp fdeps ds,ms++dms)
           where
            ms =snd (explicitlyTyped kenv tinfo [tp] ds)
	    dms = mapVars defaultName ms
	HsInstDecl s optn c tp ds     -> ([],[])
	HsDefaultDecl s t             -> ([],[])
	HsTypeSig s nms c t    -> ([],[HsVar n:>:kuscheme kenv ((ctx++c):=>t)|n<-nms])
	HsFunBind s matches           -> ([],[])
	HsPatBind s p rhs ds          -> ([],[])
	HsInfixDecl   s fixity names  -> ([],[])

        HsPrimitiveTypeDecl s ctx tp  -> (tiData ctx tp,[])
        HsPrimitiveBind s nm tp       -> ([],[HsVar nm:>:kupscheme kenv tp])
--	_ -> []
    where
      addKind (c:>:tinfo) = c:>:(kind,tinfo)
        where [kind] = [k|c':>:k<-kenv,c'==c]

      constrTypes ctx tp con =
	  case con of
	    HsConDecl s evs ectx c bangts -> -- !!!
	       [HsCon c :>: conT ectx (map unbang bangts)]
	    HsRecDecl s evs ectx c fields -> -- !!!
	       (HsCon c :>: conT ectx args):
	       [HsVar f :>: kupscheme kenv (lhsT `hsTyFun` t)|(f,t)<-fs]
	     where
               fs = [(f,t)|(fs,bt)<-fields,let t=unbang bt,f<-fs]
	       args = map snd fs
	where
	  conT ectx args = kuscheme kenv (ectx:=>funT (args++[lhsT]))
	  lhsT = tp
{-
instance (Fresh i,TypeId i,Printable i,
	  TypeCheck i e1 (Typed i e2),
	  DefinedNames i p1,TypeCheck i p1 (Typed i p2),
	  DefinedNames i ds1,Printable ds1,TypeCheckDecls i ds1 ds2,
          HasMethodSigs ds1,HasTypeAnnot i e2,
          HasBaseStruct d2 (Dinst i e2 p2 ds2),HasDef ds2 d2,

          -- Extra stuff for constructing field selector functions:
	  HasDef ds1 d1,HasBaseStruct p1 (PI i p1),
	  HasBaseStruct e1 (Einst i e1 p1 ds1),

          -- Extra stuff for translating class and instance declarations
          -- (using module TiClassInst2):
          ValueId i,HasId i e1,HasId i p1,
	  HasBaseStruct d1 (Dinst i e1 p1 ds1),Printable d1,
	  HasId i e2,HasId i p2,HasAbstr i d2,HasAbstr i ds2,
	  HasBaseStruct e2 (Einst i e2 p2 ds2),DefinedNames i p2,
	  --GetSigs i [Pred i] (Pred i) ds2,DeclInfo i ds2,
	  MapDefinedNames i ds2,
	  AddDeclsType i ds2)
      => TypeCheckDecl i (Dinst i e1 p1 ds1) ds2 where tcDecl = tcD
-}
tcD bs d =
  posContext' (srcLoc d) "(type check)" $
  case d of
    HsTypeDecl s tp t             -> retOne (hsTypeDecl s tp t)
    HsNewTypeDecl s ctx tp cd drv -> retOne (hsNewTypeDecl s ctx tp cd drv)
    HsDataDecl s ctx tp cds drv   -> tcDataDecl d bs s ctx tp cds drv
    HsClassDecl s c tp fdeps ds   -> tcClassDecl s c tp fdeps ds
    HsInstDecl s optn c tp ds     -> tcInstDecl s optn c tp ds
    HsDefaultDecl s t             -> retOne (hsDefaultDecl s t)
    HsTypeSig s nms c tp          -> retOne (hsTypeSig s nms c tp)
    HsFunBind s matches           -> oneDef # tcFunBind bs s matches
    HsPatBind s p rhs ds          -> oneDef # tcPatBind bs s p rhs ds
    HsInfixDecl   s fixity names  -> retOne (hsInfixDecl s fixity names)

    HsPrimitiveTypeDecl s ctx tp  -> retOne (hsPrimitiveTypeDecl s ctx tp)
    HsPrimitiveBind s nm tp       -> oneDef # tcPrimBind bs s nm tp

retOne = return . oneDef

tcDataDecl d bs s ctx tp cds drv =
    retOne (hsDataDecl s ctx tp cds drv)
{-
    do selfns <- tcSelFns [d] bs cds
       return (hsDataDecl s ctx tp cds drv `consDef` selfns)
-}

tcPrimBind bs s nm t =
  do t' <- varinst' bs nm
     t'=:=t
     return $ hsPrimitiveBind s nm t

tcFunBind bs s matches@(HsMatch _ n _ _ _:_) =
  do ms :>: ts <- unzipTyped # mapM tcMatch matches
     t <- varinst' bs n
     mapM_ (t=:=) ts
     return $ hsFunBind s ms

varinst' bs n =
  case [ t |HsVar x:>:t<-bs,x==n] of
    t:_ -> return t
    _ -> tfresh -- needed for selector functions generated in tcSelFns...
	 --fail$"Type checker bug: no type introduced for: "++pp n

tcMatch (HsMatch s n ps rhs ds) =
  do (ps',ds',rhs'):>:t <- tcDsLambda' ps ds rhs
     HsMatch s n ps' rhs' ds' >: t

tcPatBind bs s p rhs ds =
  do p':>:tp <- extendts ((map (fmap mono) bs)) (tc p)
     (ds',rhs'):>:trhs <- tcDsRhs ds rhs
     tp=:=trhs
     return (hsPatBind s p' rhs' ds')

tcDsRhs ds rhs =
  do ds':>:bs <- tcLocalDecls ds
     rhs':>:trhs <- extendts bs (tc rhs)
     (ds',rhs')>:trhs


{-+
Type synonyms may not be recursive (H98 report, section 4.2.2).
This check has to be made before type checking, since recursive type
synonyms can cause the current implementation of the type checker to loop!
-}
checkTypeSynRec ds =
    unless (null recsyns) $ 
      declContext recsyns $
        fail "Recursive type synonym"
  where
    recsyns = [syn|(syn,_)<-g,syn `elem` reachable' g [syn]]
    g = [(i,free) | Just d@(HsTypeDecl s tp t)<-map basestruct ds,
	            let free=freeTypeNames t,
	            i<-definedTypeNames tp]

{-+
The superclass relation must be not be cyclic (H98 report, section 4.3.1).
This check has to be made before type checking, since a cyclic superclass
relation can cause the current implementation of the type checker to loop!
-}
checkClassRec ds =
    unless (null recclasses) $ 
      declContext recclasses $
        fail "The superclass relation must be not be cyclic"
  where
    recclasses = [c|(c,_)<-g,c `elem` reachable' g [c]]
    g = [(i,free) | Just d@(HsClassDecl s ctx tp fdeps ds)<-map basestruct ds,
	            let free=freeTypeNames ctx,
	            i<-definedTypeNames tp]
