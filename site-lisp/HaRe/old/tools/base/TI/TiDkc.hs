-- Kind checking for base langauge declarations (the D structure)
module TiDkc where
import Data.List(nub,(\\))
import Data.Maybe(mapMaybe)

import HsDeclStruct
import HsExpStruct(EI)
import HsDeclMaps(accConDecl,mapFunDeps,seqFunDeps)
import FreeNamesBase() -- instance for HsType
import SrcLoc1(srcLoc)
import TI
import TiKEnv(domain)
import TiT(kcPred,kcStar,kcCheck)
import MUtils
import PrettyPrint(pp)

-- Type checking is restricted to these instances of the D & E structures:
type Dinst i e p ds = DI i e p ds (Type i) [Pred i] (Type i)
type Einst i e p ds = EI i e p ds (Type i) [Pred i]

instance (KindCheck i d ()) => KindCheck i [d] () where
  kc = mapM_ kc

instance (TypeVar i,{-DeclInfo i ds,-}KindCheck i ds ())
      => KindCheck i (Dinst i e p ds) () where
  kc = kiD

kc_ d = kc d -- >> done

{-
kiDs :: (DeclInfo [d],KindCheck [d] ())
        => [Dinst e p [d]] -> KI [Typing QId (Kind,TypeInfo)]
-}
{-
kiD :: (DeclInfo [d],KindCheck [d] ())
       => Dinst e p [d] -> KI (KInfo i)
-}
kiD d =
  posContext' (srcLoc d) "(kind check)" $
  case d of
    HsTypeDecl    s tp t           -> kcType tp t
    HsNewTypeDecl s ctx tp cd drv  -> kcData ctx tp $ kcCD cd
    HsDataDecl    s ctx tp cds drv -> kcData ctx tp $ mapM_ kcCD cds
    HsClassDecl   s c tp fdeps ds  -> kcClass c tp fdeps ds $ kc_ ds
    HsInstDecl    s optn c tp ds   -> kcInst c tp ds
    HsDefaultDecl s t              -> mapM_ kcStar t -- >> return [] -- hmm
    HsTypeSig     s nms c tp       -> kcSig c tp
    HsFunBind     s matches        -> done --return []
    HsPatBind     s p rhs ds       -> done --return []
    HsInfixDecl   s fixity names   -> done --return []

    HsPrimitiveTypeDecl s ctx tp   -> kcData ctx tp done
    HsPrimitiveBind    s nm tp     -> kcSig (tail [tp]) tp

kcInst ctx tp ds =
  do kcLhs kpred ctx tp $ done
     kc ds -- there shouldn't be any explicit type info here to check, but ...

kcType tp t =
  do k <- fresh
     kcLhs k [] tp (kcCheck k t)
kcData ctx tp rhs = kcLhs kstar ctx tp rhs
kcClass ctx tp fdeps ds rhs = kcLhs kpred ctx tp rhs

kcLhs :: TypeVar i => Kind -> [Pred i] -> Type i -> KI i () -> KI i ()
kcLhs k ctx tp rhs =
  do vs <- return [] --kintro (freeTyvars (ctx,tp))
     extendkts vs $ do mapM_ kcPred ctx
                       k' <- kc tp
		       k'=*=k
		       rhs

kcCD cd = accConDecl ((>>).kcStar) ((>>).mapM_ kcPred) cd done

kcSig ctx t =
  do --freevs <- domain # getKEnv
     vs <- return [] --kintro (freeTyvars (ctx,t) \\ freevs)
     extendkts vs $ do mapM_ kcPred ctx
                       kcStar t
     --return []

--------------------------------------------------------------------------------

tiType tp t = [c:>:syn]
  where c   = definedType tp
	syn = Synonym (typeParams tp) t

tiNewtype = tiData' Newtype
tiData = tiData' Data
tiData' d ctx tp = [definedType tp:>:d]

tiClass kenv tinfo ctx tp fdeps0 ds = [c:>:Class ctx kvs fdeps ms]
  where
    kvs = kinded kenv vs
    vs = typeParams tp
    ps = zip vs [0..] -- 0-based parameter positions

    fdeps =
      mapMaybe cleanDep $ -- silently ignore duplicates and trivial deps!!
      fromJust' "TiDkc.hs: undefined type variable in functional dependency" $
      seqFunDeps $
      mapFunDeps (flip lookup ps) $
      fdeps0++concatMap superDeps ctx

    cleanDep (xs0,ys0) = if null ys then Nothing else Just (xs,ys)
      where xs = usort xs0
	    ys = usort ys0 \\ xs

    ms = map (fmap unquant) $ snd (explicitlyTyped kenv tinfo [] ds)
    unquant (Forall avs vs' qt) = Forall avs (vs'\\kvs) qt
    c = definedType tp
    --_:>:k = kinded1 kenv c
 -- Check that method types don't restrict any class variables (vs)!

    superDeps p = maybe [] deps ((Just >#< mapM isVarT)=<<flatConAppT p)
      where
        deps (c,vs) =
          case [fdeps|c':>:Class _ _ fdeps _<-tinfo,c'==c] of
            [fdeps] -> mapBoth (map (vs!!)) fdeps
	    _ -> []
