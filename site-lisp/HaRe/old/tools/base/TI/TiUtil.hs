{-+
This module defines some basic type checking functions, and some utility
functions, notably functions for type checking applications (#tapp#) and
identifiers (#inst# et al), introducing fresh type/kind variables,
recording constraints on types/kinds and instantiating type schemes.
-}
module TiUtil where
import TiMonad
import TiTypes
import TiSolve(TypeConstraint(..))
import TiNames(ValueId,TypeVar,dictName,dictName')
import TiClasses
import TiKinds(KindConstraint(..))
import TiFresh
import HasBaseStruct
import HsConstants(mod_Prelude,tuple)
import BaseSyntax(srcLoc,TI(..))
import TypedIds(NameSpace(..))
import PrettyPrint hiding (var)
import MUtils

--import IOExts(trace) -- debug

-- How to type check applications:
-- tapp :: HasCoreSyntax e => TI (Typed e) -> TI (Typed e) -> TI (Typed e)
fun `tapp` arg =
  do (f:>:tf) <- fun
     (a:>:ta) <- arg
     r <- appt tf ta
     f `app` a >: r
 where
    -- First case is an optional optimization
    appt (Typ (HsTyFun fa fr)) ta = do fa =:= ta
				       return fr
    appt tf ta = do r <- tfresh
	            tf =:= ta `hsTyFun` r
		    return r

--typedTuple :: HasCoreSyntax e => [Typed e] -> Typed e
typedTuple ets =
    do t <- tupleType ts
       TiClasses.tuple es>:t
  where es:>:ts = unzipTyped ets

--tcList :: HasCoreSyntax e => [Typed e] -> TI (Typed e)
tcList ets =
  do let es:>:ts = unzipTyped ets
     t <- allSame ts
     listType <- getListType
     list es >: listType t

tupleType ts =
   do t <- prelTypeName (HsConstants.tuple (length ts-1))
      return $ foldl hsTyApp (hsTyId t) ts

getListType = hsTyApp . hsTyId # prelTypeName "[]"
getBoolType = hsTyId # prelTypeName "Bool"

allSame [] = tfresh
allSame (t:ts) = mapM_ (t=:=) ts >> return t

stdValue = stdName ValueNames
stdType  = stdName ClassOrTypeNames
stdClass = stdType

prelValue     = stdValue . (,) mod_Prelude
prelTypeName  = stdType  . (,) mod_Prelude
prelClassName = prelTypeName
prelTy n = hsTyId # prelTypeName n

instStd = inst @@ stdValue
instStd_srcloc s = inst_srcloc s @@ stdValue
instPrel = inst @@ prelValue
instPrel_srcloc s = inst_srcloc s @@ prelValue

--inst :: HasCoreSyntax i e => HsIdentI i -> TiMonad.TI i (Typed i e)
inst x = inst_loc' Nothing x
inst_loc x = inst_loc' (Just (srcLoc x)) x
inst_srcloc s = inst_loc' (Just s)

inst_loc' s x =
  do sc@(Forall ags gs qt) <- sch x
     vs <- freshvars gs
     let ctx:=> t = freshen' vs (tdom gs) qt
     ds <- newdicts s ctx
     foldl1 app (spec x sc (map tyvar vs):map var ds) >: t

inst_field f =
  do ctx:=>t <- instsch f
     ds <- newdicts Nothing ctx -- use srcLoc f!!
     return t -- hmm

instsch f = sinst =<< sch f
sinst (Forall ags gs qt) =
  do vs <- freshvars gs
     return (freshen' vs (tdom gs) qt)

freshvars gs =
    do vs <- freshlist (length gs)
       addvars (zipTyped (vs:>:ks))
       return vs
  where
    vs0:>:ks = unzipTyped gs

freshInst :: (TypeVar i,Fresh i,ValueId i)
          => Scheme i -> TiClasses.TI i ([Typing i (Pred i)],Type i)
freshInst (Forall ags gs qt) =
  do ctx:=>t <- freshen (tdom gs) qt
     ds <- map dictName # freshlist (length ctx)
     return (zipTyped ((ds{-::[QId]-}):>:ctx),t)

newdicts s ds = mapM (newdict s) ds
newdict s pred = do d <- flip dictName' s # fresh
	            addinst (d:>:pred)
		    return d

{-
freshdicts ctx =
  do idns <- map dictName # freshlist (length ctx)
     return (zipWith (:>:) idns ctx)
-}

freshen gs t =
  do vs <- freshlist (length gs)
     return (freshen' vs gs t)

freshen' vs gs t = apply s t
  where s = S [(g,tyvar v) | (g,v) <- zip gs vs]


allfresh t = freshen (tv t) t

varinst x =
  do Forall [] [] ([] :=> t) <- sch (HsVar x)
     return t


infix 4 =:=,=*=
t1 =:= t2 = constrain (t1:=:t2)
k1 =*= k2 = constrain (k1:=*k2)

addinst = constrain . Inst
addkinst ki = do --trace (pp $ "addkinst"<+>ki) $ return ()
                 constrain (KInst ki)

-- Introduce new types of kind *:
tintro xs = do ts <- freshlist (length xs)
	       addtypes ts
	       return (zipTyped (xs:>:ts))

-- Introduce monomorphic type schemes for types of kind *:
schintro xs = map (fmap mono) # tintro xs

-- Introduce new kind variables:
kintro xs = do ts <- freshlist (length xs)
	       return (zipTyped (xs:>:ts))

tfresh = do t <- fresh
	    addtype t
	    return t

addvars = mapM_ (addkinst.emap tyvar)
addtypes ts = mapM_ addtype ts
addtype t = addkinst (t:>:kstar)
