module NewTiMonad(
   IM,--TI,KI,
   KEnv,
   getEnv,getTEnv,getKEnv,getIEnv,getModule,getDefaults,
   extendts,extend,extend1,extendkts,extendEnv,extendIEnv,inModule,inEnv,
   env,kenv,sch,kindOf,constrain,getConstraints,
   (>:),errmap,freshInt
  ) where
import HsIdent(HsIdentI)
import HsName(ModuleName(..))
import TiTypes
--import TiKinds(Kind,TypeInfo{-,KindConstraint-})
import TiEnv(lookup,extenv1,extenv)
import qualified TiEnv(Env,empty)
import TiInstanceDB(IDB,emptyIdb,extendIdb)
import TiConstraints(Constraints,empty,single,merge)
import MUtils
import Lift
import PrettyPrint(pp)

import MT(MT(..))
import OutputMT
import StateMT
import EnvMT
import ExceptM

import qualified Tree

type TEnv i = TiEnv.Env (HsIdentI i) (Scheme i) -- type of value identifiers
type KEnv i = TiEnv.Env (HsIdentI i) (Kind,TypeInfo i)   -- kind of type identifiers

data TiEnv i  = Env { inMod::FilePath->ModuleName,
		      monomorph::Bool, -- use the monomorpism restriction?
		      defaults::[[Type i]], -- from all default(t1,...,t2)
		      kenv::KEnv i,
		      tenv::TEnv i,
		      idb::IDB i }

emptyEnv = Env (const (Module "nomodule")) True [] TiEnv.empty TiEnv.empty emptyIdb

-- IM should really be an abstract type!
type IM i c = WithOutput c 
            ( WithEnv (TiEnv i) 
            ( WithState Unique
            ( ExceptM Error ))) 

--type TI i   = IM i (TypeConstraint i)
--type KI i   = IM i KindConstraint
type Error  = String
type Unique = [Int]


errmap f m = do e <- getEnv
                s <- getSt
                case withStS s (withEnv e (removeOutput m)) of
                  Left x -> raise (f x)
                  Right ((a,t),s) -> setSt_ s >> outputTree t >> return a

run :: TiEnv i -> IM i c a -> Either Error a
run env = removeExcept . withSt [1..] . withEnv env . fmap fst . removeOutput

instance Monad m => Lift (IM i c) m where
  lift = either fail return . run emptyEnv

getConstraints :: IM i c a -> IM i d (a, Tree.T c)
getConstraints m = MT.lift (removeOutput m)

typeError :: Error -> IM i c a
typeError err = raise err

constrain :: c -> IM i c ()
constrain c = output c

modEnv :: (TiEnv i -> TiEnv i) -> IM i c a -> IM i c a
modEnv f  = inModEnv f
modTEnv f = modEnv (\env@Env{tenv=e}->env{tenv=f e})
modKEnv f = modEnv (\env@Env{kenv=e}->env{kenv=f e})
modIEnv f = modEnv (\env@Env{idb=e}->env{idb=f e})

getTEnv :: IM i c (TEnv i)
getTEnv = tenv # getEnv

getKEnv :: IM i c (KEnv i)
getKEnv = kenv # getEnv

getIEnv :: IM i c (IDB i)
getIEnv = idb # getEnv

getModule :: IM i c (FilePath->ModuleName)
getModule = inMod # getEnv

getDefaults :: IM i c [[Type i]]
getDefaults = defaults # getEnv

extend1 x t = modTEnv (extenv1 x t)
extend x    = modTEnv (extenv x)
extendts ts = extend [(x,t)|x:>:t<-ts]

extendk1 x t  = modKEnv (extenv1 x t)
extendk x     = modKEnv (extenv x)
extendkts ts  = extendk [(x,t)|x:>:t<-ts]

extendEnv (ks, ts) = extendkts ks . extendts ts
extendEnv' (ks, ts) = extendk ks . extend ts

extendIEnv x  = modIEnv (extendIdb x)

inModule m d = modEnv (\env->env{inMod=m,defaults=d})

env proj x =
  do env <- getEnv
     case TiEnv.lookup (proj env) x of
       Nothing -> typeError ("Not in scope: "++pp x{-++" in "++show (proj env)-})
       Just sch -> return sch

sch x = env tenv x
kindOf x = fst # env kenv x

freshInt :: IM i c Int
freshInt = head # updSt tail

infix 4 >:
(>:) :: e -> t -> IM i c (Typing e t)
e >: t = return (e :>: t)
