{-+
This module contains experimental stuff to complete the dictionary translation
by translating class declarations to record types and instance declaration
to record values. Doing this while staying within the source abstract syntax
is a bit clumbsy, unfortunately.

The default methods in class declarations are placed
in a "default instance", i.e. a record of the same type as an instance,
from with the default methods are selected by the translation of instance
declarations.

Apart from fields corresponding to methods, the record types also contain
fields corresponding to superclasses. The context reduction function refers
to these functions.

Most of this is not used at the moment.
-}
module TiClassInst2({-tcClassDecl,tcInstDecl,-}tcInstOrClassDecl'') where
import Data.List((\\))

--import HasBaseStruct(HasBaseStruct(..),hsTypeSig,hsClassDecl,hsInstDecl)
import HasBaseStruct
import BaseSyntax hiding (TI)
--import SrcLoc(SrcLoc,srcLoc)
import TI
import qualified TiKEnv(lookup)
import TiDkc(Dinst{-,Einst-})
import TiDinst(hsSimpleBind{-,hsSimpleBind',tcSelFns-})
import TiSolve(matches)
--import MUtils
import PrettyPrint

{-
tcClassDecl d src ctx cl fdeps ds =
  do let (msigs,defaults) = splitMethodSigs ds
     (ms,ds') <- tcClassDecl' src [cl] cl defaults
     msigs':>:_ <- tcLocalDecls msigs -- kind check + type conversion
     hsClassDecl2 d {-bs-} ms src ctx cl fdeps msigs' ds'


tcInstDecl src ictx inst ds =
  do (ns,ds') <- tcInstDecl' src ictx inst ds
     modmap <- getModule
     let n = instName' modmap src
     -- return $ hsInstDecl0 n ns src ictx inst ds'
     hsInstDecl2 n ns src ictx inst ds'
-}
--------------------------------------------------------------------------------
{-
hsClassDecl2 ::
  (Printable i,ValueId i,Eq i,TypeVar i,
   HasBaseStruct d2 (Dinst i e2 p2 ds2),
   HasBaseStruct e2 (Einst i e2 p2 ds2),HasId i e2,
   DeclInfo i (Dinst i e2 p2 ds2),
   HasId i p2,
   HasDef ds2 d2,
   --GetSigs i [Pred i] (Pred i) ds2,
   HasAbstr i d2,AddDeclsType i ds2,
   HasBaseStruct e1 (Einst i e1 p1 ds1),HasBaseStruct p1 (PI i p1),
   HasDef ds1 d1,TypeCheckDecl i (Dinst i e1 p1 ds1) ds2
  ) =>
  (Dinst i e1 p1 ds1) -> MethodInfo i -> SrcLoc -> [Pred i] -> Pred i -> HsFunDeps i ->
  ds2 -> ds2 -> TI i ds2
hsClassDecl2 d1 {-bs-} mi@(ms,_,_) src ctx cl fdeps msigs ds =
    do defaultInst <- hsDefaultMethods dn mi src ctx cl ds
       --m <- getModule
       let fields =
	     [HsRecDecl src cn 
		 (supers++
		 [([i],unb (hsTyForall' vs (funT (c++[t]))))
                  | HsVar i:>:Forall vs (c:=>t)<-ms])]
       dictdata <- return $ HsDataDecl src [] cl fields []
       let dts = explicitlyTyped {-m-} [] dictdata
       selfns <- extendts dts $ tcSelFns [d1] []{-bs-} fields
       return $ addDeclsType ([],[HsVar dn:>:upscheme (funT [cl,cl])]) $
	        base dictdata
		`consDef` defaultInst
		`consDef` selfns
  where
    dn = defaultName cn
    c@(HsCon cn) = definedType cl
    supers = [([superName cn n],unb c)|(n,c)<-zip [1..] ctx]
    unb = HsUnBangedType

hsTyForall' [] t = t
hsTyForall' vs t = hsTyForall vs t

hsDefaultMethods ::
  (HasDef ds2 d2,HasBaseStruct d2 (Dinst i e p ds2),
   HasId i e,HasId i p,Eq i,ValueId i,Printable i,
   HasAbstr i d2,AddDeclsType i ds2,
   HasBaseStruct e (Einst i e p ds2))
  => i -> MethodInfo i -> SrcLoc -> [Pred i] -> Pred i -> ds2 -> TI i d2
hsDefaultMethods dn (ms,ims,_) src ctx cl ds =
    do darg <- dictName # fresh
       return $ abstract [darg] $ hsSimpleBind' src dn (body [darg]) ds
  where
    c@(HsCon cn) = definedType cl

    body dns = hsRecConstr cn (superDefs++methodDefs)
      where
        methodDefs = map methodDef ms

        superDefs = [HsField n (noDefault n)|n<-take (length ctx) superns]
           where superns = map (superName cn) [1..]

	methodDef (i@(HsVar v):>:_) =
	  HsField v $ if i `elem` ims
		      then apps (ident i:map var dns)
		      else noDefault i

	noDefault i = hsApp (var (prelVal "error"))
			    (hsLit$HsString$pp$src<>": no default for:"<+>i)

    apps = foldl1 hsApp
-}
--------------------------------------------------------------------------------

type MethodInfo i = ([Assump i],[HsIdentI i],[i])

tcInstDecl' = tcInstOrClassDecl'' False
tcClassDecl' = tcInstOrClassDecl'' True
tcInstOrClassDecl'' ::
  (TypeId i,Printable i,Fresh i,Printable dsin,
   DefinedNames i dsin,HasBaseStruct din (Dinst i e p dsin),
   HasDef dsin din,HasId i p,ValueId i,HasId i e,
   TypeCheckDecls i dsin dsout,
   HasDef dsout dout,HasBaseStruct dout (Dinst i e2 p2 dsout))
  => Bool -> SrcLoc -> [Pred i] -> Pred i -> dsin
  -> TI i (MethodInfo i,dsout)
tcInstOrClassDecl'' isClass src ictx inst ds0 =
  do let cname@(HsCon cn) = definedType inst
     (k,Class super0 cvs0 fundeps0 ms0) <- env kenv cname
     let cl0 = appT (ty cname:map tyvar (tdom cvs0))
     (cl,ms,super) <- return (cl0,ms0,super0) -- names are already unique
     --(cl,ms,super) <- allfresh (cl0,ms0,super0) --since `matches` requires disjoint vars
     supdns <- if isClass then return []
               --else map dictName # freshlist (length super)
	       else return $ map (superName cn) [1..length super]
     let ds = toDefs (map superMethod supdns) `appendDef` ds0
         ims = definedValueNames ds0 -- names of implemented methods
	 ns:>:_ = unzipTyped ms -- names of the methods of this class
	 supms = zipTyped (map HsVar supdns:>:map mono super)
     case ims \\ ns of
       badms@(_:_) ->
         fail ("Extra bindings in "++dkind++" declaration: "++pp badms)
       [] -> errorContext (pp$"In"<+>dkind<+>inst) $
             do kenv <- getKEnv
                s <- (inst `matches` cl) kenv
		let mts = (map.fmap) (addctx kenv (apply s ictx))
			             (apply s (ms++supms))
		ds' <-
		  --errmap (("Method signatures:\n"++pp mSigs++"\n")++) $
		  --errorContext ("Methods:\n"++pp ds) $
	          extendts [superVar:>:superType] $
		  tcInstDecls mts ds
	        return ((ms,ims,supdns),ds')
  where
    dkind = if isClass then "class" else "instance"
    addctx kenv ictx (Forall vs' vs (ctx:=>t)) = Forall vs' (ivs++vs) ((ictx++ctx):=>t)
       where
         ivs0 = tv (ictx,ctx,t) \\ tdom vs
	 ivs = [v:>:kind v|v<-ivs0]
	 kind = maybe err fst . TiKEnv.lookup kenv . HsVar
	 err = error "Bug in TiClassInst2: missing kind for a type variable"

--    mSig m@(HsVar n) = do Forall vs (ctx:=>t) <- sch m
--		          return $ hsTypeSig src [n] (ictx++ctx) t
    superMethod n = hsSimpleBind src n (ident superVar)

    superVar = HsVar (prelVal "super")
    superType = forall' [av:>:kpred] ([a]:=>a)
      where a = tyvar av
	    av = tvar 1

--------------------------------------------------------------------------------
{-
hsInstDecl2 ::
  (Eq i,ValueId i,
   HasDef ds2 d2,AddDeclsType i ds2,
   HasId i e2,HasId i p2,HasAbstr i ds2,
   HasBaseStruct e2 (Einst i e2 p2 ds2),
   HasBaseStruct d2 (Dinst i e2 p2 ds2))
  => i -> MethodInfo i -> SrcLoc -> [Pred i] -> Pred i -> ds2 -> TI i ds2
hsInstDecl2 n (ms,ims,supsels) src ctx inst ds =
    do self:dns <- map dictName # freshlist (1+length ctx)
       let selfbody = body self dns
       return $ abstract dns $
         let ds' = addDeclsType ([],[HsVar self:>:mono inst]) $
	           consDef selfdef ds
             selfdef = hsSimpleBind src self selfbody
         in oneDef $ hsSimpleBind' src n (var self) ds'
  where
    c@(HsCon cn) = definedType inst
    dn = defaultName cn

    body self dns = hsRecConstr cn (superDefs++methodDefs)
      where
        methodDefs = map methodDef ms

        superDefs = zipWith methodDef' superns (map HsVar supsels)
           where superns = map (superName cn) [1..]

	methodDef (i@(HsVar v):>:_) =
	  HsField v $ if i `elem` ims
		      then apps (ident i:map var dns)
		      else useDefault i

	methodDef' v i = HsField v $ apps (ident i:map var dns)

	useDefault i = ident i `hsApp` (var dn `hsApp` (var self))

    apps = foldl1 hsApp
-}
