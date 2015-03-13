-- Kind inference for the T structure
module TiT where
import HasBaseStruct
import BaseSyntaxStruct
import TI hiding (TI)
--import MUtils

instance (TypeVar i,KindCheck i t Kind)
      => KindCheck i (TI i t) Kind where
  kc t =
    case t of
      HsTyFun t1 t2   -> do kcStar t1; kcStar t2; return kstar
--    HsTyTuple ts    -> do mapM_ kcStar ts; return kstar
      HsTyApp t1 t2   -> kc t1 `kapp` kc t2
      HsTyVar v       -> kindOf (HsVar v)
      HsTyCon c       -> kindOf (HsCon c)
      HsTyForall vs ps t' -> {-do bs <- kintro (map HsVar vs)
			     extendkts bs $-} mapM_ kcPred ps >> kc t'

instance (TypeVar i,KindCheck i t Kind)
      => KindCheck i (Qual i t) Kind where
  kc (ps:=>t) = do mapM_ kcPred ps; kc t

kcCheck k t = do k'<-kc t; k'=*=k
kcStar t = kcCheck kstar t
kcPred t = kcCheck kpred t

fun `kapp` arg =
  do kf <- fun
     ka <- arg
     k <- fresh
     kf =*= ka `karrow` k
     return k

instance TypeVar i => KindCheck i (Type i) Kind where
  kc (Typ t) = kc t

