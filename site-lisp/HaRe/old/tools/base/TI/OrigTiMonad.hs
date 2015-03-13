{-# OPTIONS -fglasgow-exts #-}
{-# LANGUAGE MultiParamTypeClasses, OverlappingInstances, UndecidableInstances, FunctionalDependencies, NoMonomorphismRestriction #-}
module OrigTiMonad(
   IM,run,--TI,KI,
   KEnv,
   getEnv,getTEnv,getKEnv,getIEnv,getModule,getDefaults,getStdNames,
   extendts,extend,extend1,extendkts,extendEnv,extendIEnv,
   inModule,inEnv,withStdNames,
   env,kenv,sch,kindOf,stdName,stdSch,constrain,getConstraints,monomorphism,
   monomorphismRestriction,
   errorContext,errorContext',posContext,posContext',declContext,moduleContext,
   (>:),freshInt
  ) where
import Prelude hiding (lookup) -- for Hugs
import Control.Monad(MonadPlus(..))
import HsIdent(HsIdentI)
import HsName(ModuleName,Id,noModule)
import TiTypes
import TiKEnv(KEnv,lookup,extenv1,extenv)
import qualified TiKEnv(empty)
import TiTEnv(TEnv)
import qualified TiTEnv(lookup,extenv1,extenv,empty)
import TiInstanceDB(IDB,emptyIdb,extendIdb)
import TiConstraints(Constraints,empty,single,merge)
import DefinedNamesBase(NameSpace)
import TiError
import MUtils
import ExceptM()
import Lift
import PrettyPrint(Printable,pp,(<+>),(<>),ppi,vcat)

--type TEnv i = TiEnv.Env (HsIdentI i) (Scheme i) -- type of value identifiers
--type KEnv i = TiEnv.Env (HsIdentI i) (Kind,TypeInfo i) -- kind of type identifiers

data TiEnv i  = Env { inMod::FilePath->ModuleName,
		      stdNames::NameSpace->(ModuleName,Id)->Either String (HsIdentI i),
		      monomorphism::Bool, -- use the monomorpism restriction?
		      defaults::[[Type i]], -- from all default(t1,...,t2)
		      kenv::KEnv i,
		      tenv::TEnv i,
		      idb::IDB i }

emptyEnv = Env (const noModule) noStdNames
	       True [] TiKEnv.empty TiTEnv.empty emptyIdb
  where
    noStdNames ns (m,n) =
      fail $ pp $
        "Bug: no standard entities provided to the type checker:"<+>m<>"."<>n

newtype IM i c ans = IM { unIM::TiEnv i->Unique->Err i (Out c ans) }
--type TI i = IM i (TypeConstraint i)
--type KI i = IM i KindConstraint

type Err i ans = Either (Error (HsIdentI i)) ans

data Out c ans = Out ans (Unique,Constraints c)
type Unique = [Int]

instance Functor (Out i) where
  fmap f (Out ans out) = Out (f ans) out

instance Functor (IM i c) where
  fmap f (IM m) = IM $ \ env ids -> fmap (fmap f) (m env ids)

instance Monad (IM i c) where
  return ans = IM $ \ env ids -> Right (Out ans (ids,empty))

  IM m1 >>= xm2 =
     IM $ \ env ids0 ->
     case m1 env ids0 of
       Left err -> Left err
       Right (Out x (ids1,out1)) ->
         case unIM (xm2 x) env ids1 of
	   Left err -> Left err
	   Right (Out y (ids2,out2)) -> Right (Out y (ids2,merge out1 out2))

  fail = typeError . Other . vcat . lines

instance MonadPlus (IM i c) where
  mzero = fail "No error message provided (PFE programmer used mzero or msum)"
  IM m1 `mplus` IM m2 =
     IM $ \ env ids0 ->
     case m1 env ids0 of
       Left _ -> m2 env ids0
       r -> r

errmap f (IM m) =
  IM $ \ env ids ->
  case m env ids of
    Left err -> Left (f err)
    Right y -> Right y

inContext       ctx = errmap (InContext ctx)
errorContext'   txt locs = inContext (OtherCtx (ppi txt) locs)
errorContext    txt = errorContext' txt []
posContext  loc     = inContext (AtPos loc Nothing)
posContext' loc txt = inContext (AtPos loc (Just (ppi txt)))
moduleContext   ms  = inContext (ModuleCtx ms)
declContext     is  = inContext (DeclCtx is)

run (IM m) =
  case m emptyEnv [1..] of
    Left err -> Left err
    Right (Out ans (_,cs)) -> Right ans

instance (Printable i,Monad m) => Lift (IM i c) m where
  lift = lift . run

getConstraints (IM m) =
 IM $ \ env ids ->
 case m env ids of
   Left err -> Left err
   Right (Out ans (ids,cs)) -> Right (Out (ans,cs) (ids,empty))

typeError err = IM $ \ env ids -> Left err

constrain c = IM $ \ env vs -> Right (Out () (vs,single c))

modEnv f (IM m) = IM $ m . f
modTEnv f = modEnv (\env@Env{tenv=e}->env{tenv=f e})
modKEnv f = modEnv (\env@Env{kenv=e}->env{kenv=f e})
modIEnv f = modEnv (\env@Env{idb=e}->env{idb=f e})
monomorphismRestriction on = modEnv (\env->env{monomorphism=on})

getEnv = IM $ \ env ids -> Right (Out env (ids,empty))
getTEnv = tenv # getEnv
getKEnv = kenv # getEnv
getIEnv = idb # getEnv
getModule = inMod # getEnv
getStdNames = stdNames # getEnv
getDefaults = defaults # getEnv

extend1 x t = modTEnv (TiTEnv.extenv1 x t)
extend bs = modTEnv (TiTEnv.extenv bs)
extendts ts = extend [(x,t)|x:>:t<-ts]

extendk1 x t = modKEnv (extenv1 x t)
extendk bs = modKEnv (extenv bs)
extendkts ts = extendk [(x,t)|x:>:t<-ts]

extendEnv (ks, ts) = extendkts ks . extendts ts
--extendEnv' (ks, ts) = extendk ks . extend ts

extendIEnv env = modIEnv . extendIdb $ env

--inEnv env = modEnv (const env)
inEnv env (IM m) = IM $ \ _ -> m env

inModule m d = modEnv (\env->env{inMod=m,defaults=d})
withStdNames stdNames = modEnv (\env->env{stdNames=stdNames})

env' lookup x =
  do env <- getEnv
     case lookup env x of
       Nothing -> fail ("Not in scope: "++pp x{-++" in "++show (proj env)-})
       Just sch -> return sch

env proj = env' (TiKEnv.lookup . proj)

stdName ns o = do f <- getStdNames
	          lift (f ns o)

stdSch ns = sch @@ stdName ns

sch x = env' (TiTEnv.lookup . tenv) x
kindOf x = fst # env kenv x

freshInt = IM $ \ env (id:ids) -> Right (Out id (ids,empty))

infix 4 >:
(>:) :: e -> t -> IM i c (Typing e t)
e >: t = return (e :>: t)
