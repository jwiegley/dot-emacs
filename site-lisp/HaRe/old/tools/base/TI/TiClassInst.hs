-- Type checking for class and instances declarations.
module TiClassInst where
import Data.List((\\))
import Data.Maybe(fromMaybe)

import HasBaseStruct(hsClassDecl,hsInstDecl,hsId,hsLit,hsApp,hsPId,hsPatBind)
import HsLiteral
import HsGuardsStruct
--import TiPrelude(prelError)
--import SrcLoc(SrcLoc,srcLoc)
import TI
--import TiDkc(Dinst)
--import TiSolve(matches)
import PrettyPrint
import MUtils
import TiClassInst2(tcInstOrClassDecl'')

tcClassDecl src ctx cl fdeps ds = -- a quick hack...
  do mnames <- methodNames cl -- or extract mnames from msigs...
     prelError <- prelValue "error"
     let (msigs,defaults) = splitMethodSigs ds
	 lacksDefault = mnames \\ definedValueNames ds
         defaultDefaults = toDefs (map (defaultDefault prelError) lacksDefault)
	 defds = defaults `appendDef` defaultDefaults
     ds' <- mapDefinedNames defaultName # tcClassDecl' src [cl] cl defds
     msigs':>:_ <- tcLocalDecls msigs -- kind check + type conversion
     return $
       hsClassDecl src ctx cl fdeps (rmDeclsType msigs') `consDef` ds'
  where
    defaultDefault prelError m = hsPatBind src (hsPId m) (HsBody body) noDef
       where
         body = hsId prelError `hsApp`
                hsLit src (HsString ("No default for method "++pp m))

tcInstDecl src optn ictx inst ds =
  do mnames <- methodNames inst
     let lacksDef = mnames \\ definedValueNames ds
         defds = toDefs (map useDefault lacksDef)
	 mds = ds `appendDef` defds
     ds' <- tcInstDecl' src ictx inst mds
     modmap <- getModule
     let n = fromMaybe (instName' modmap src inst) optn
     return $ oneDef $ hsInstDecl src (Just n) ictx inst ds'
  where
    useDefault m@(HsVar v) = hsPatBind src (hsPId m) (HsBody (hsId dm)) noDef
      where dm = HsVar (defaultName v)

methodNames cl =
  do Class _ _ _ ms <- snd # env kenv (definedType cl)
     let mnames:>:_ = unzipTyped ms
     return mnames

tcInstDecl' = tcInstOrClassDecl' False
tcClassDecl' = tcInstOrClassDecl' True

{-
tcInstOrClassDecl'
  :: (TypeId i,Printable i,Fresh i,
      Printable dsin, DefinedNames i dsin,
      TypeCheckDecls i dsin dsout)
  => Bool -> SrcLoc -> [Pred i] -> Type i -> dsin -> TI i dsout
-}
tcInstOrClassDecl' isClass src ictx inst ds =
  snd # tcInstOrClassDecl'' isClass src ictx inst ds
{-
tcInstOrClassDecl' isClass src ictx inst ds =
  do let cname = definedType inst
     (k,Class super0 cvs0 fundeps0 ms0) <- env kenv cname
     let cl0 = appT (ty cname:map tyvar cvs0)
     (cl,ms) <- allfresh (cl0,ms0) --since `matches` requires disjoint vars
     let ims = definedValueNames ds
	 ns:>:_ = unzipTyped ms
     case ims \\ ns of
       badms@(_:_) ->
         fail ("Extra bindings in "++dkind++" declaration: "++pp badms)
       [] -> errmap (("In "++dkind++" "++pp inst++"\n")++) $
             do s <- inst `matches` cl =<< getKEnv
		let mts = (map.fmap) (addctx (apply s ictx))
			             (apply s ms)
		ds' <-
		  --errmap (("Method signatures:\n"++pp mSigs++"\n")++) $
		  tcInstDecls mts ds -- (toDefs mSigs `appendDef` ds)
	        return ds'
  where
    dkind = if isClass then "class" else "instance"
    addctx ictx (Forall vs (ctx:=>t)) = uscheme ((ictx++ctx):=>t)
--  mSig m@(HsVar n) = do Forall vs (ctx:=>t) <- sch m
--		          return $ hsTypeSig src [n] (ictx++ctx) t
-}
