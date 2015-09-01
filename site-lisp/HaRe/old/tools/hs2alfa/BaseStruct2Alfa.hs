module BaseStruct2Alfa{-(transModule,modPath)-} where
import TiDecorate(DeclsUseType,TiPat(..),drop_use)
import TiPrelude(prelFlip,prelOtherwise,prelTrue)
import PNT(PNT(..))
import TypedIds(IdTy(ConstrOf,Class),ConInfo(..),TypeInfo(..))
import UniqueNames as UN(PN(..),Orig(..),orig)
import HasBaseName
import NameMaps
import NameMapsDecorate
import QualNames(unqual,getQualified)
import BaseSyntax hiding (extend)
import Syntax(kstar,kpred,kprop)
import HsConstants(mod_Prelude)
import PrettyPrint
import qualified UAbstract as U
import qualified AbstractOps as U
import qualified UMatch as U
import qualified USubstitute as U
import qualified UFree as U
--import qualified DrawOptions as U(defaultArgOptions,HasName(..),ArgOptions(..))
--import qualified DrawOptionsPrinter as U(printIdOptions)
import EnvM hiding (inEnv)
import MUtils
import TI hiding (TI,getEnv,inst,tapp,sch,inEnv,extend,restrict,tupleT,conName)
--import TiT(kcCheck)
--import RemovePatBinds(remPatBinds')
--import RemoveIrrefPatsBase(removeIrrefPats)
import Lift(lift)
import TiHsName
import USCC(decls)
import PFE0(moduleInfoPath) -- grr

--import Char(isUpper)
import Maybe(fromMaybe,listToMaybe,fromJust)
import List(nub,partition,(\\),sort)
import Monad(join,mplus{-,unless-})
--import Fudgets(ctrace)

default(Int)

type DEnv = DeclsType NName
type DEnv' = DeclsUseType NName
type Env = ([ModuleName],DEnv) -- to keep track of which module is being translated
type Ctx = [Typing NName (Pred NName)]
--type NName = PN HsName
type NName = PNT

---

modPath m = moduleInfoPath m++".alfa"

class Trans src dst | src->dst where
  trans :: src->EnvM Env dst
  transTyped :: Maybe (HsTypeI NName) -> src -> EnvM Env dst

  -- Defined at least one of trans and transTyped!
  trans = transTyped Nothing
  transTyped _ = trans

instance Trans src dst => Trans (Maybe src) (Maybe dst) where
  transTyped t (Just e) = Just # transTyped t e
  transTyped t Nothing = return Nothing

ltrans xs = mapM trans xs

--instance Trans [HsImportDeclI i] [U.Decl] where
--  trans is = return [] -- not implemented yet

instance (Trans ds1 [U.Def],
	  --MapNames (Bool,NName) ds1 NName ds2,
          AccNames NName ds1,
	  MapNames NName ds0 NName ds1)
      => Trans (HsModuleI m i1 ds0) U.Module where
  trans m = transModule m # getEnv

packageSynonym (PlainModule newm) (PlainModule oldm) = -- !!!
  [U.decl' [U.defA $
            U.Package (U.Var (transMName newm),(U.ctx [],
                       U.PackageInst (un (transMName oldm))))]]

joinModuleNames [m] = m
joinModuleNames ms = PlainModule . concat $ sort [s|PlainModule s<-ms] -- !!!

uPackage n ds = U.defA $ U.Package (n,(U.ctx [],U.PackageDef ds))
uPack n ds = uPackage n (decls ds)

transModule hsmodule (mo0,denv) =
      U.Module (map include origMods++
                [U.decl' [uPackage (U.Var m)
                              (map openUnqual (unqualNames ns)++
                               decls (withEnv env (trans ds2)))]]
		)
    where
      PlainModule m = transM (joinModuleNames mo0) -- !!!
      mo = map transM mo0
      HsModule src _ e is ds0 =
          {-remPatBinds' bind_names . removeIrrefPats arg_names $-} hsmodule
{-
	where
	  --arg_names, bind_names :: [PNT]
	  arg_names   = [ localVal ("arg" ++ show n) | n <- [1..]] 
	  bind_names  = [ localVal ("bind" ++ show n) | n <- [1..]] 
-}
      env = (mo,denv)
      ds2 = {-mapNames snd-} ds1
      ds1 = transNames mo ds0

      ns = --map snd $
	   filter notcon $ {- nubBy eqSrc $ -} accNames (:) ds1 []

      --notcon = fst
      notcon (PNT _ (ConstrOf {}) _) = False
      notcon _ = True

      origMods = nub [m|PNT (PN _ (G m _ _)) _ _<-ns,m `notElem` mo0]

      include m = U.ImportDecl (U.Import (modPath m))

      unqualNames ns =
         collectByFst [(m,n)|PNT (PN (UnQual n) (G m _ _)) _ _<-ns,m `notElem` mo0]

      openUnqual (PlainModule m,ns) = -- !!!
	  U.decl' [U.defA (U.Open (un (transMName m),map oa (nub ns)))]

oa = oav . U.Var . transName
oav' v = U.OpenArg [] v Nothing
oav v = oav' v Nothing

mapPNT f (PNT i idty p) = PNT (f i) idty p

transNames self = mapNames2 TopLevel (varf,conf)
    where
      varf (role,ClassOrTypeNames) = mapPNT (u . tvar)
      varf (role,ValueNames)       = mapPNT (u . var)
      conf (role,ClassOrTypeNames) = mapPNT (u . tcon)
      conf (role,ValueNames)       = mapPNT (u . vcon)

      -- Packages can't refer to themselves...
      u (PN (Qual m n) o) | m `elem` self = PN (UnQual n) o
      u x = x

--    var (PN (UnQual x) o@(I m _)) = PN (Qual (transM m) x) o -- instances
      var (PN (UnQual x) o@(D n _)) = PN (UnQual (x++show n)) o -- type vars
      var (PN (UnQual x) o@(Sn _ s)) = PN (UnQual (x{-++sh s-})) o
--       where sh (SrcLoc f 0 0) = ""
--	       sh (SrcLoc f r c) = "_"++show r++"_"++show c
      var (PN (Qual _ _) o@(G m n _)) = PN (Qual (transM m) (transName n)) o
      var v@(PN q o) =
              if v==prelVal "super"
	      then localVal "super" -- hack
	      else PN (transQ q) o

      tvar (PN (UnQual x) o@(D n _)) = PN (UnQual (x++show n)) o -- generated type var
      tvar (PN (UnQual x) o@(UN.S s)) = PN (UnQual (x++"_")) o -- source type var

      vcon (PN _ o@(G m n _)) = PN (UnQual (transConName n)) o
      vcon c = c

      tcon (PN (Qual _ _) o@(G m n _)) = PN (Qual (transM m) (transTCon n)) o
      tcon (PN (UnQual _) o@(G m n _)) = PN (UnQual (transTCon n)) o

      transTCon n =
        case n of
          "[]" -> "List"
	  _ -> transName n

      transQ (UnQual x) = UnQual (transName x)
      transQ (Qual m n) = Qual (transM m) (transName n)


transConName n = case n of
                   "[]" -> "Nil"
                   ":" -> "Cons" -- Hmm. Alfa Library convension
		   _ -> transName n

inPrelude this = transM mod_Prelude `elem` this
transM (PlainModule m) = PlainModule (transMName m)
transM (MainModule m) = PlainModule (transMName "Main") -- !!!
transMName m = "Module_"++dots2uscore m

transName n = 
  case n of
    "Type" -> "Type_" -- reserved identifier
    "sig" -> "sig_"
    "use" -> "use_"
    "." -> ".." -- reserved operator
    "()" -> "Unit"
    '(':s -> "Tuple"++show (length s) -- tuples!
    _ -> n

transD ds = decls # trans ds

{-
instance Trans Ctx [U.Def] where trans = ltrans

instance Trans (Typing NName (Pred NName)) U.Def where
   trans (d:>:t) = do t' <- trans t
		      d' <- transVar d
		      return $ valdef d' ([],t') U.ePreMetaVar
-}

inModDEnv f = inModEnv (apSnd f)
extend env = inModDEnv (env+++)
extendFrom ds = extend (drop_use (envFrom ds))

extendTyvars = extendTyvars' . mapFst HsVar
extendTyvars' vs = inModDEnv (\(ks,ts)->(map tyvar vs++ks,ts))
  where tyvar (v,k) = v:>:(k,Tyvar)

restrict vs = inModDEnv (\(ks,ts)->(ks,[a|a@(x:>:_)<-ts,x `notElem` vs]))
restrictFrom ps = restrict (patternVars ps)
scope ps ds = restrictFrom ps . extendFrom ds

instance (Printable e,Printable p,Printable ds,Printable t,Printable ctx,
	 FreeNames NName ctx,
	 Printable tp,DefinedNames NName tp,DefinedNames NName t,
	 FreeNames NName t,KindCheck NName t Kind,Types NName t,
	 FreeNames NName tp,Trans p U.Pat,
	 HasId NName p, DefinedNames NName p, AccNames NName p,
	 KindCheck NName tp Kind,Types NName tp,
	 HasId NName e,Trans e U.Exp,Trans ds [U.Def], EnvFrom ds DEnv',
         Trans t U.Exp,Trans ctx [U.Exp],Trans tp U.Exp) =>
	 Trans (DI NName e p ds t ctx tp) [U.Def] where
  trans d = trans' d =<< getMEnv
    where
      trans' d this =
	  case d of
	    HsTypeDecl s tp t             -> tPs tp $ typeD # tlhs tp <# trans t
	    HsNewTypeDecl s ctx tp cd drv -> tPs tp $ dataD # tlhs tp <# ltrans [cd]
	    HsDataDecl s ctx tp cds drv   -> tPs tp $ dataD # tlhs tp <# ltrans cds
	    HsClassDecl s ctx tp _ ds     -> pPs tp $ classD ds =<< tlhs tp
	    HsInstDecl s optn c tp ds     -> iPs c tp $ instDecl s optn c tp ds
      --    HsDefaultDecl s t             -> return (hsDefaultDecl s t)
            HsTypeSig s nms c tp          -> return [] -- just looks ugly...
	    HsFunBind s matches           -> transMatches matches
	    HsPatBind s p rhs ds          -> transPatBind p rhs ds
      --    HsInfixDecl   s fixity names  -> return (hsInfixDecl s fixity names)
	    HsPrimitiveTypeDecl s ctx tp  -> tPs tp $ primTypeD # tlhs tp
	    HsPrimitiveBind s i t         -> primValueD i t
	    _ -> return [commentdef d]
	where
          pPs = kPs kpred
	  tPs = kPs kstar

	  kPs k lhs m =
             do vks <- runKc k (freeTyvars lhs) lhs
                extendTyvars' vks m

	  iPs ctx lhs m =
             do vks <- runKc kpred (freeTyvars (ctx,lhs)) lhs
                extendTyvars' vks (m [(v,k)|(HsVar v,k)<-vks])

	  tlhs tp  = do (qn, ts) <- U.flatApp' # trans tp
			let HsCon n = definedType tp
			    n' = U.Var (getQualified (getBaseName n))
			k <- kinfo tp
			return (n,n',k,[x|U.EVar x<-ts])

	  kinfo tp = do (k,i) <- knd (definedType tp)
			k' <- trans k
			return (k',i)

     -- A hack to be able to use special syntax when defining types in the Prelude:
	  --unqual (U.EVar n) = n
	  --unqual (U.EProj (U.EVar (U.Var m)) (U.Label s)) = U.Var s

	  typeD (_,n,(k,_),xs) t = [valdef n (args xs k) t]

	  dataD lhs@(_,n,(k,_),xs) cs =
	      if inPrelude this && reusePreludeFromAlfa n
	      then primTypeD lhs
	      else [valdef n (args xs k) (U.ESum cs)]
            where
	      reusePreludeFromAlfa n =
                 n `elem` map U.Var ["Unit","Bool","List"]

          --methodnames ms = ltrans [n|HsVar n<-ns]
          --  where ns:>:_ =unzipTyped ms
          methodnames ms = [U.Var ("method_"++show i)|i<-[1..length ms]]

	  classD ds (n,n'@(U.Var nstr),(k,TI.Class ctx vs fdeps ms0),_) =
	      do let ss=zipWith superMethod [1..] ctx
                     ms=ss++ms0
                 vs' <- ltrans (tdom vs)
		 ms' <- ltrans ms
		 let ns' = methodnames ms
		 ds' <- trans{-D-} ds -- default methods
		 let tsig = args vs' k
		     cn = {-projSelf-} (U.EVar n')
		     c = U.app cn (map U.EVar vs')
		 mds <- concatMapM (methodDecl c ns' vs') (zip ns' ms)
		 return $ valdef n' (args vs' k) (sig ns' ms'):
			  defaultMethods ds'++
			  mds
	    where
	      d = U.Var "d"
	      (cvs,_) = U.flatFun k

{-
	      defaultMethods ds' =
                  U.defA $ U.Package (pkg,(U.ctx [],U.PackageDef ds'))
	        where pkg = U.Var ("default__"++nstr)
-}
	      defaultMethods = map (U.mapDefB defaultMethod)
	      defaultMethod (U.Value (U.Var name,rhs)) =
	        U.Value (U.Var (defaultName name),rhs)
	      defaultMethod (U.Binding (U.Var name,rhs)) =
	        U.Binding (U.Var (defaultName name),rhs)
	      defaultMethod d = d -- comments...

	      methodDecl c ns' vs' (n',HsVar m:>:s) =
		do (gs,qt) <- kcScheme m s
                   gs' <- ltrans gs
		   qt' <- extendTyvars gs (trans qt)
		   let ps = zip vs' cvs++gs'++[(d,c)]
		   m' <- transUnqualVar m
		   return $ hide m' ps ++
			    [valdef m' (ps,([],qt'))
				    (sigproj ns' n' (map (U.EVar . fst) gs'))
				    ]

              superMethod i supercl =
	         HsVar (superName n i):>:mono supercl

              sigproj ns' m' gs' =
                U.app (U.EProj (U.EVar d) (var2lbl m')) gs'
              dataproj ns' m' gs' =
                U.ECase (U.EVar d) [U.Branch (inst,(ns',U.app (U.EVar m') gs'))]

              sig ns ms = U.ESig (zipWith method ns ms)
                where
		  method n (U.SigField x t) = U.SigField (var2lbl n) t

              sig2data _ ms =
                U.ESum [U.Constr (inst,(U.ctx [(lbl2var x,t)|U.SigField x t<-ms],[]))]
	  inst = U.Con "instance"

	  primTypeD (_,n,(k,_),xs) = 
	      [if inPrelude this
	       then preludePrimImportD n
	       else postulate n (args xs k)]

	  preludePrimImportD n =preludePrimImportD' n Nothing
	  preludePrimImportAsD n = preludePrimImportD' n . Just
	  preludePrimImportD' n as =
	      U.changeProps (const [U.Public]) $
	      U.defA (U.Open (pb,[oav' n as]))
	    where
	      pb = un "PreludeFromAlfa"

	  --instDecl s Nothing ctx tp ds vks = undefined
	  instDecl s (Just n) ctx tp ds vks =
	      do ctx' <- trans ctx
		 vks' <- ltrans vks
		 t <- trans tp
		 --ds' <- transD ds
                 ds' <- trans ds
		 ns <- do (k,TI.Class super _ _ ms) <- kinfo tp
			  let ns=[n|HsVar n:>:_<-ms]
                              HsCon c=definedType tp
			      ss=map (superName c) [1..length super]
			  ltrans (ss++ns)
		 let mns = methodnames ns
		 n' <- trans n
		 let dicts = xargs ctx'
                     actx = vks'++dicts
		     targs = map (U.EVar . fst) vks'
		 return $
	           --hide n' vks' ++
                   [valdef n' (actx,([],t)) (str targs dicts (zip ns mns) ds')]
            where
	      str targs dicts ns2mns ds =
                  U.EStr (decls (map (U.mapDefB (rename.adjust)) (bindings ds)))
	        where
                  adjust (U.Binding (n,e)) = U.Binding (n,adjustmethod e targs dicts)
		  adjust d = d

	          rename (U.Value (name,rhs)) = U.Value (mname name,rhs)
	          rename (U.Binding (name,rhs)) = U.Binding (mname name,rhs)
	          rename d = d -- comments...

                  mname n = fromJust (lookup n ns2mns)
{-
	      str2con targs dicts ns ds = U.app (U.ECon inst) (map conarg ns)
	        where
	          conarg n = fromMaybe undef (lookup n ds')
	          ds' = [(n,adjustmethod e targs dicts)|
                          U.DefA _ (U.Binding (n,e))<-bindings ds]
-}
              adjustmethod e = substds . uapply e

	      --useDefault (U.Var n) = un (defaultName n)
              --undef = U.ePreMetaVar
	      --undef = eUndefined `uApp` U.ePreMetaVar

          bindings = U.rmTypeSign . map (U.mapDefB preserve)
	    where
	      preserve d =
	        case d of
                  U.Value (name,(ctx@(U.Ctx _ (_:_)),e,t)) | needType e ->
                    U.Value (name,(ctx,eTyped e t,t))
                  _ -> d

              needType (U.ECase {}) = True
	      needType _ = False -- sig and data can't occur in instance decls

          ifHasType v d m = ifM (inEnv (HsVar v)) m (return [commentdef d])
	  transMatches ms@(HsMatch _ n _ _ _:_) =
	      ifHasType n ms $
	      do sch@(gs,cs:=>t) <- schk (HsVar n)
		 extendTyvars gs $ do
		   cs' <- ltrans cs
		   (xs,rhs) <- umatch this (matchcons ms) # ltrans ms
		   (targs,tres) <- U.flatFun # trans t
		   --this <- getMEnv
		   tctx <- ltrans gs
		   let (ctx,(xs',tres')) = args' xs (cs'++targs) tres
		       cnt = length gs+length cs'
		   n' <- transUnqualVar n
		   return $
	             --commentdef sch:
                     hide' n' cnt++[valdef n' (tctx++ctx,(xs',tres')) rhs]

	  transPatBind = transVarBind . fromJust' . isVar 

          fromJust' = fromMaybe (error "Hs2Alfa.hs: pattern bindings not supported")
	  transVarBind qv rhs ds =
            ifHasType qv d $
	    do v <- transUnqualVar qv
	       (gs,[]:=>t) <- schk (HsVar qv)
	       tvs <- ltrans gs
	       extendTyvars gs $ do
		 t' <- trans t
		 extendFrom ds $ do
		   rhs' <- transR ds rhs
		   return $ hide v gs ++ [valdef v (tvs, ([],t')) rhs']


	  primValueD qv t =
	    do v <- transUnqualVar qv
	       if inPrelude this 
	         then return [preludePrimImportD v]
		 else do (gs,[]:=>t) <- schk (HsVar qv)
			 tvs <- ltrans gs
			 extendTyvars gs $ do
			   t' <- trans t
			   return $ hide v gs ++ [postulate v (tvs, ([], t'))]

commentdef d = U.defA $ U.CommentDef (comment (pp d))

args xs t = uncurry (args' xs) (U.flatFun t)
args' [] ts tres = ([],([],U.eFuns ts tres))
args' (x:xs) (t:ts) tres = apFst ((x,t):) (args' xs ts tres)
args' xs [] tres = ([],(xs,tres))

{- This was used in an attempt to put type and class declarations inside
 packages, where auxiliary functions could be put as well without creating
name clashes. But packages can't be recursive so it didn't work.
-}
--packdef v lhs rhs = uPackage v (decls [valdef self lhs rhs])
--self = U.Var "T"
--projSelf e = U.EProj e (U.Label "T")

valdef v (ctx,(xs, t)) rhs =
  U.defA $ U.Value (v,(U.ctx ctx,U.uAbsExp xs (rmtannot rhs),t))

rmtannot (U.ETyped e t) = e
rmtannot e = e

typeOf (U.ETyped e t) = Just t
typeOf _ = Nothing

postulate v (ctx,(xs, t)) = U.defA $ U.Axiom (v,(U.ctx ctx,U.uAbsExp xs t))
--typedef v ctx rhs = U.defA $ U.Type (v,(U.ctx ctx,rhs))

eTyped e@(U.ETyped _ _) t = e
eTyped e t = U.ETyped e t

instance (HasId NName e,Trans e U.Exp,Trans p U.Pat,DefinedNames NName p,
	  Trans ds [U.Def],EnvFrom ds DEnv')
          => Trans (HsMatchI NName e p ds) U.Rule where
  trans (HsMatch s _ ps rhs ds) =
    (,) # ltrans ps <# (scope ps ds $ transR ds rhs)

transR ds e = eLet # transD ds <# trans e

instance Trans t U.Exp => Trans (HsConDeclI NName t c) U.Constructor where
  -- Existential quantification is ignored!!! (Impredicativity problem)
  trans (HsConDecl s _ _ n as) = constr # transCon n <# mapM (trans.unbang) as
    where
      constr n as = U.Constr (nilHack n,(args as,[]))
      unbang bt = accBangType const bt ()
      args = U.ctx . xargs

      nilHack (U.Con "List") = U.Con "Nil"
      nilHack c = c
  trans (HsRecDecl s _ _ n fs) = constr # transCon n <# concatMapM transFields fs
    where
      transFields (fs,bt) = fields # mapM trans fs <# trans (unbang bt)
        where fields fs t = [(f,t)|f<-fs]
      constr n as = U.Constr (n,(U.ctx as,[]))

xargs = zipWith arg [1..]
  where arg i t = (U.Var ("x"++show i),t)

instance (HasId NName e,Trans e U.Exp) => Trans (HsRhs e) U.Exp where
  transTyped t (HsBody e) = transTyped t e
  transTyped t (HsGuard gs) = transGuards gs =<< trans t
    where
       -- this is a quick hack!!!
      transGuards [] t =
          do this <- getMEnv
             return (eUndefined this `uApp` opt "result type in guarded rhs" t) -- a failed guard
      transGuards ((_,g,e):gs) t =
          if isTrue g
	  then trans e
          else eIf t # trans g <# trans e <# transGuards gs t

      isTrue = maybe False isTrueId . isId
      isTrueId x = x `elem` [prelTrue,prelOtherwise]

instance Trans (Assump NName) U.SigPart where
  trans (HsVar x:>:t) = U.SigField # transLbl x <# trans t

instance Trans (Scheme NName) U.Exp where
  trans s =
    do (vs,qt) <- kcScheme "?" s
       U.piExp # ltrans vs <# extendTyvars vs (trans qt)

instance Trans t U.Exp => Trans (Qual NName t) U.Exp where
  trans (ctx:=>t) = U.eFuns # ltrans ctx <# trans t

instance Trans (HsTypeI NName) U.Exp where trans (Typ t) = trans t
instance Trans NName U.Var where trans x = U.Var # (flip transId x # getMEnv)

transEVar x = inst x
{-
  do b <- inEnv x
     if b
      then do Forall vs (ctx:=>_) <- sch x  --  monomorphic recursive call
	      unless (null vs && null ctx) $
	         error $"missing type annotation for "++show x
	      x' <- inst x
	      vs' <- map U.EVar # ltrans vs
	      return $ U.app x' (vs'++replicate (length ctx) U.ePreMetaVar)
      else inst x -- lambda bound variable
-}

-- Constructors don't need type arguments, but they need to be applied
-- to the right number of values.
transECon c sc ts =
    con # inst c <# trans (specialize sc ts)
  where
    con c t =
       eTyped (U.absExp (zipWith (U.:-) ps ts) (U.app c (map U.EVar ps))) t
      where
	(ts,tr) = U.flatFun t
        ps = [U.Var ("conarg"++show n)|n<-[1..length ts]]

    specialize (Forall _ gs qt) ts = apply (TI.S (zip (tdom gs) ts)) qt

instance (Printable t,KindCheck NName t Kind,Trans t U.Exp,Types NName t)
       => Trans (TI NName t) U.Exp where
  trans t =
    case t of
      HsTyFun x y  -> U.eFun # trans x <# trans y
--    HsTyTuple ts -> U.app . tupleT (length ts) # getMEnv <# ltrans ts
      HsTyApp f x  -> trans f `tapp` trans x
      HsTyVar nm   -> do b <- inTEnv (HsVar nm)
		         if b
			    then do (k,_) <- knd (HsVar nm)
			            if k==kprop
				       then U.EApp (un "predT") # inst (HsVar nm)
				       else inst (HsVar nm)
			    else return (missing "type variable not in scope")
      HsTyCon nm   -> instTcon nm
      HsTyForall vs ps t1 ->
          do vks <- runKc kstar (map HsVar vs) t1
	     let vks' = [(v,k)|(HsVar v,k)<-vks] -- grr
             U.piExp # ltrans vks' <# extendTyvars' vks (trans t1) -- ps !!!

--ePis vs t = foldr ePi t vs
--ePi (v,k) = U.EPi (v U.:- k)
{-
tupleT n this = uqn (tupleName n)
  where
    prel = transM mod_Prelude
    uqn = if this==prel then un else qn prel
-}
tupleName n = "Tuple"++show (n::Int)

instance Trans Kind U.Exp where
  trans (K k) =
    case k of
      Kstar -> return eStar
      Kfun k1 k2 -> U.eFun # trans k1 <# trans k2
      Kpred -> return eClass
      Kprop -> return ePropKind

consE = U.ECon cons
nilE  = U.ECon nil
cons  = U.Con "Cons"
nil   = U.Con "Nil"

{-
type Pat0 = (U.Con,[U.Var])

instance Trans HsPat Pat0 where
  trans (Pat p) =
    case p of
      HsPId (HsCon c) -> return (transCon c,[])
      HsPApp c ps -> return (transCon c,transPVars ps)
      HsPList []  -> return (nil,[])
-}

instance Trans (TiPat NName) U.Pat where
  trans (Pat p) = trans p
  trans (TiPSpec (HsVar v) _ []) = U.PVar # transUnqualVar v
  trans (TiPSpec (HsCon c) _ _) = con0P c
  trans (TiPTyped p t) = transTyped (Just t) p
  trans (TiPApp p1 p2) = papp # trans p1 <# trans p2
    where
      papp (U.PCon c ps) p = U.PCon c (ps++[p])
      papp _ _ = U.PVar noname -- !!!

  trans p = --error $ "Not implemented yet: "++pp p
	  return $ U.PVar noname -- !!!

  transTyped t (Pat e) = transTyped t e
  transTyped _ e = trans e

-- ...

instance (Printable p,Trans p U.Pat) => Trans (PI NName p) U.Pat where
  trans p =
    case p of
      HsPId (HsCon c) -> con0P c
      HsPId (HsVar v) -> U.PVar # transUnqualVar v
      HsPApp c ps -> U.PCon # transCon c <# ltrans ps
      HsPList  s ps -> foldr consP nilP # ltrans ps
      HsPTuple s ps -> U.PCon (tupleCon (length ps)) # ltrans ps
      HsPInfixApp p1 c p2 -> U.PCon # transCon c <# ltrans [p1,p2]
      HsPParen p -> trans p
      HsPAsPat v p -> U.PAs # trans v <# trans p
      HsPWildCard -> return $ U.PVar noname
      HsPIrrPat p -> trans p -- !!
      _ -> --error $ "Not implemented yet: "++pp p
           return $ U.PVar noname -- !!!

noname = U.Var "__" -- "_" is reserved in Agda nowadays

nilP = U.PCon nil []
consP p1 p2 = U.PCon cons [p1,p2]
con0P c = flip U.PCon [] # transCon c

tupleCon = U.Con . tupleName

--rmtrans e = rmtannot # trans e
rmltrans es = map rmtannot # ltrans es

ptrans (TiPTyped p t) = (,) # trans p <# trans t
lptrans = mapM ptrans

optTransTyped t e = maybe e (eTyped e) # trans t

{-
checkChar x c = 
  if c<toEnum 0 || c>toEnum 255
  then error$ "Unsupported char"++show (fromEnum c)++" in "++show x
  else c
-}
checkChar _ c = toEnum (fromEnum c `mod` 256) -- hmm

instance (HasId NName e,Trans e U.Exp,
	  --AccNames NName p,DefinedNames NName p,HasId NName p,Trans p U.Pat,
	  Trans ds [U.Def],EnvFrom ds DEnv')
	 => Trans (EI NName e (TiPat NName) ds c t) U.Exp where
  transTyped t e =
    optTransTyped t =<<
    case e of
      HsId x                 -> transEVar x
      HsLit _ (HsChar c)     -> return (U.EChar (checkChar c c))
      HsLit _ (HsString s)   -> return (U.EString (map (checkChar s) s))
      --HsLit _ (HsString s)   -> return (U.EString "") -- for a performance test
      HsLit _ (HsInt i)      -> return (U.EInt i)
      HsLit _ (HsFrac x)     -> return (U.ERat x)
      HsLit _ _              -> return (missing "unimplemented type of literal")
      HsInfixApp x op z      -> inst op `tapp` trans x `tapp` trans z
      HsApp x y              -> trans x `tapp` trans y
--    HsNegApp x             -> inst prelNegate `tapp` tc x
      HsLambda ps e          -> do this <- getMEnv
                                   eLambda this (patscons ps) # lptrans ps <# restrictFrom ps (trans e)
      HsLet ds e             -> eLet # transD ds <# extendFrom ds (trans e)
      HsIf x y z             -> eIf # trans t <# trans x <# trans y <# trans z
      HsCase e alts          -> do this <- getMEnv
                                   eCase this (altcons alts) # trans t <# trans e <# ltrans alts
--    HsDo stmts             -> tcStmts stmts
      HsTuple es             -> U.app (U.ECon (tupleCon (length es))) #rmltrans es
      HsList es              -> foldr (U.app2 consE) nilE # rmltrans es
      HsParen e              -> trans e
      HsLeftSection x op     -> inst op `tapp` trans x
      HsRightSection op y    -> inst pqFlip `tapp` inst op `tapp` trans y
--    HsRecConstr s n fields   -> recConstr n fields
  --  HsRecUpdate e upds     ->
--     HsEnumFrom x           -> inst prelEnumFrom `tapp` tc x
--    HsEnumFromTo x y       -> inst prelEnumFromTo `tapp` tc x `tapp` tc y
--    HsEnumFromThen x y     -> inst prelEnumFromThen `tapp` tc x `tapp` tc y
--    HsEnumFromThenTo x y z ->
--	inst prelEnumFromThenTo `tapp` tc x `tapp` tc y `tapp` tc z
--    HsListComp stmts       -> emap hsListComp # tcLComp stmts
--    HsExpTypeSig s e c t    -> tcExpTypeSig s e c t
      -- Unimplemented things are turned into metavariables:
      _                      -> return $ missing "unimplemented form of expression"
   where
{-   recConstr c fs =
       case fieldsOf c of
         Nothing -> return $ missing bad
         Just fns -> do c' <- inst (HsCon c)
			let args = map (pick [(orig fn,e)|HsField fn e<-fs]) fns
			args' <- mapM (mtrans bad) args
			return (U.app c' args')

     bad = "bad record construction?"

     fieldsOf (PNT c (ConstrOf _ tinfo) _) =
       fmap (map orig) . join . listToMaybe $
	 [conFields ci|ci<-constructors tinfo,orig (conName ci)==orig c]
     fieldsOf (PNT c (TypedIds.Class ms) _) = Just (map orig ms)
     fieldsOf _ = Nothing -- Not a constructor ?!

     pick = flip lookup
-} 
     pqFlip = mapHsIdent oqual prelFlip


oqual (PNT (PN _ o@(G m n _)) t s) = PNT (PN (Qual m n) o) t s
oqual n = n

mtrans s Nothing = return $ missing s
mtrans s (Just e) = trans e

instance (Trans i1 i2,Trans e1 e2) => Trans (HsFieldI i1 e1) (i2,e2) where
  trans (HsField i e) = (,) # trans i <# trans e

instance Trans [HsTypeI NName] [U.Exp] where trans = ltrans

instance (Trans a1 a2,Trans b1 b2) => Trans (a1,b1) (a2,b2) where
  trans = trans >#< trans

instance (HasId NName e,Trans e U.Exp,Trans p U.Pat,DefinedNames NName p,
	  Trans ds [U.Def],EnvFrom ds DEnv')
         => Trans (HsAlt e p ds) U.Rule
  where
    trans (HsAlt s p rhs ds) =
        do p' <- trans p
	   scope p ds $ do
	     rhs' <- transR ds rhs
	     return ([p'], rhs')

sets xs = [(x,eStar)|x<-xs]
--sets xs = [(x,U.ePreMetaVar)|x<-xs]

instTcon c = {-projSelf # -} inst (HsVar c)

inst x = flip inst' x # getMEnv

inst' this (HsCon x) = U.ECon (transCon' this x)
inst' this (HsVar n) = case getBaseName (n::NName) of
		         UnQual  x -> un x
			 Qual mo x -> qn mo x

qn (PlainModule m) x = U.EProj (un m) (U.Label x)
un = U.EVar . U.Var
--evar = U.EVar . U.Var

{-
transPVar p = transVar (fromJust' . isVar $ p)
  where fromJust' = fromMaybe (error "BaseStruct2Alfa.hs: patterns in lambdas are not supported")
transPVars ps = mapM transPVar ps
-}

-- This is used to translate identifiers appearing where only unqualified names
-- are legal, but the abstract syntax allows qualified names
transUnqualVar = transVar . unqual

transCon x = flip transCon' x # getMEnv
transVar x = flip transVar' x # getMEnv

var2lbl (U.Var x) = U.Label x
lbl2var (U.Label x) = U.Var x
transLbl x = var2lbl # transUnqualVar x

transVar' this = U.Var . transId this
transCon' this = U.Con . transId this

--lbl = U.Label # transId

transId this n = transId' this (getBaseName (n::NName))

transId' this (UnQual x) = x
transId' this (Qual mo@(PlainModule m) x) = -- !!!
    if mo `elem` this
    then x
    else m{-++"_"-}++x
               --Hmm. Qualified names in definitions won't work...
	       --Just output something rather than failing immediately.


eClass = un "Class" -- for readability
eStar = un "Star" -- for readability
--eStar = U.eSet -- avoids dependency on nonstd predefined things in Alfa
ePropKind = un "PropKind" -- for readability
eUndefined this =
  if inPrelude this
  then un "undefined"
  else qn (transM mod_Prelude) "undefined"

eLet [] e = e
eLet (U.Decl _ []:ds) e = eLet ds e
eLet ds e = U.ELet ds e -- problem if e is case or sig or ...

eCase this css t e rules = optTyped t (U.subst e v ecase)
  where ([v],ecase) = umatch this css rules

optTyped = maybe id (flip eTyped)

eLambda this css tps e0 =
    if all uIsVar ps
    then U.absExp [x U.:-t|(U.PVar x,t)<-tps] e0
    else U.absExp [v U.:-t|(v,t)<-zip vs ts] (f ecase)
  where
    (ps,ts) = unzip tps
    (vs,ecase) = umatch this css [(ps,e)]
    (e,f) = case e0 of
	      U.ETyped e t -> (e,flip eTyped t)
	      _ -> (e0,id)

altcons alts = patscons [ p | HsAlt s p rhs ds<-alts]
matchcons ms =  patscons [ p | HsMatch s _ ps rhs ds<-ms,p<-ps]

-- This can fail if a pattern contains constructors from different types
-- but with the same unqualified name...
patscons = transCons . accCons
  where
    transCons = (listcons:).map (mapFst con)
    con (PN c o) = U.Con (transConName c)

    listcons = [(U.Con "Nil",0),(U.Con "Cons",2)]

    --tr x = ctrace "cons" x x

accCons ps = accNames con ps []
  where
    con (PNT c (ConstrOf _ tinfo) _) css =
	if cs `elem` css
	then css
	else cs:css
      where cs = tinfo2cs tinfo
    con _ css = css

    tinfo2cs tinfo = [(c,n)|ConInfo{conName=c,conArity=n}<-constructors tinfo]


eIf t cnd thn els = eIfTyped (opt "result type for if" t') cnd thn els
  where t' = t `mplus` typeOf thn `mplus` typeOf els

eIfTyped t cnd thn els = U.app (un "if_then_else") [t,cnd,thn,els]
--eIf cnd thn els = U.ECase cnd [b "True" thn,b "False" els]
--  where b c e = U.Branch (U.Con c,([],e))

umatch this css rules =
  case rules of
    [(ps,e)] | all uIsVar ps -> ([x|U.PVar x<-ps],e) -- to preserve var names
    _ -> U.exhaustiveMatch'' css [] rules undef
  where
    undef = eUndefined this `uApp` missing "potential pattern match failure"

uIsVar (U.PVar _) = True
uIsVar _ = False

m1 `tapp` m2 = uApp # m1 <# m2

e1 `uApp` e2 =
  case e1 of
    -- Agda doesn't like applied meta variables:
    U.EMeta _ -> e1
    U.EAnnot a (U.EMeta _) -> e1
    -- Agda doesn't like beta redexes:
    U.ETyped (U.EAbs (x U.:-_) e1') (U.EPi _ t) -> U.subst e2 x e1' `eTyped` t
    U.EAbs x e1' -> uLet x e2 e1'
    --U.ETyped e1' (U.EPi _ t) -> (e1' `uApp` e2) `eTyped` t
    _ ->  U.EApp e1 e2
  where
    -- Avoid code duplication, if possible without name capture
    -- (there are no non-recursive declarations in Agda)
    uLet (x U.:-t) e2 e1 = 
      if x `elem` U.free e2
      then U.subst e2 x e1
      else U.ELet [U.decl' [valdef x (([],([],t))) e2]] e1

getDEnv = snd # getEnv
getMEnv = fst # getEnv

{-+
Since the type checker doesn't provide kind information for type variables in
type schemes, we do a _local_ kind inference on the type scheme.
I am not quite sure this is enough to always get the right kinds...
-}
schk x = kcScheme x =<< sch x
schak x = akcScheme x =<< sch x

kcScheme  _ (Forall _  vs qt) = return ([(v,k)|v:>:k<-vs],qt)
akcScheme _ (Forall as vs qt) = return ([(v,k)|v:>:k<-as++vs],qt)
{-
kcScheme x (Forall [] qt) = return ([],qt) -- shortcut
kcScheme x (Forall vs qt) =
  do vks <- runKc' x kstar (map HsVar (tdom vs)) qt
     return ([(v,k)|(HsVar v,k)<-vks],qt)
--}
--runKcStar = runKc kstar

runKc = runKc' ""
runKc' s  k vs qt =
  do kenv <- fst # getDEnv
     vkts <- lift (errorContext (pp (s,vs,qt,k)) $
                   extendkts kenv $ kgeneraliseSloppy $
                   do bs <- kintro vs
		      bs' <- kintro (map HsVar (tv qt)\\vs) -- hmm
                      k' <- extendkts (bs++bs') $ kc qt
		      let _ = k' `asTypeOf` k
	              return bs)
     return [(v,k)|v:>:(k,_)<-vkts]

sch x = lookupts x . snd # getDEnv
knd x = lookupts x . fst # getDEnv

inEnv x = (elem x . map tfst . snd) # getDEnv
inTEnv v = (elem v . map tfst . fst) # getDEnv

tfst (x:>:_) = x

lookupts x [] = error ("Not in scope:"++show x)
lookupts x ((y:>:t):ts) = if x==y then t else lookupts x ts

eCmnt = U.eComment . comment
comment s = "{- "++s++" -}"
annot s = "{-# Alfa "++s++" #-}"

missing s = eCmnt s U.ePreMetaVar
opt = fromMaybe . missing

hide v = hide' v . length

hide' (U.Var v) cnt =
    if cnt>0
    then [U.defA $ U.CommentDef $ annot s]
    else []
  where
    s = --U.printIdOptions (U.name v,(U.defaultArgOptions v){U.hideCnt=cnt})
        "var "++show v++" hide "++show cnt
---}

uapply e [] = e
uapply (U.EAbs (x U.:-_) e) (a:as) = uapply (U.subst a x e) as
uapply e as = U.app e as -- hmm

substds e [] = e
substds e@(U.EAbs p@(x U.:-t) b) ds =
    case partition (sameT t) ds of
      ((d,_):ds1,ds2) -> substds (U.subst (U.EVar d) x b) (ds1++ds2)
      ([],ds2) -> U.EAbs p (substds b ds2) -- assume p is a type parameter
      -- _ -> U.eComment (comment $ "Something went wrong here: dictionary argument type mismatch: "++show t) e -- Hmm
  where
    sameT t (_,t') = t==t'
substds e _ = U.eComment (comment "Something went wrong here: too many dictionary arguments?") e -- Hmm
