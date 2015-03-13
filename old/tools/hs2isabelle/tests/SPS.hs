-- Synchronous stream processors
module SPS where

newtype S i o = S (i->(o,S i o))
feed (S sps) i = sps i


runS _       []     = []
runS sps (i:is) = continue (feed sps i) is
continue c is = fst c:runS (snd c) is

mapS_sps f i = (f i,S (mapS_sps f))

mapS f = S (mapS_sps f)

mapAccumS_sps f s1 i =
  case f s1 i of (s2,o2) -> (o2,S (mapAccumS_sps f s2))

mapAccumS f s0 = S (mapAccumS_sps f s0)

--(>*<) :: S i1 o1 -> S i2 o2 -> S (i1,i2) (o1,o2)
sps1 >*< sps2 = S (sps_times sps1 sps2)
sps_times sps1 sps2 (i1,i2) =
  case feed sps1 i1 of
    (o1,s1) -> case feed sps2 i2 of
      (o2,s2) -> ((o1,o2), s1 >*< s2)

(>+<) :: S i1 o1 -> S i2 o2 -> S (Either i1 i2) (Either o1 o2)
sps1 >+< sps2 = S (sps_plus sps1 sps2)

sps_plus sps1 sps2 (Left  i1) = case feed sps1 i1 of (o1,sps1') -> (Left  o1,sps1'>+<sps2)
sps_plus sps1 sps2 (Right i2) = case feed sps2 i2 of (o2,sps2') -> (Right o2,sps1>+<sps2')

sps1 -<- sps2 = S (sps_compose sps1 sps2)
sps_compose sps1 sps2 i2 = 
  case feed sps2 i2 of
    (o2,sps2') -> case feed sps1 o2 of
      (o1,sps1') -> (o1,sps1'-<-sps2')

assert Separation1 = {-#cert:Separation1#-}
  All sps1 . All sps2 . All is1 . All is2 .
  {runS (sps1>*<sps2) (zip is1 is2)} === {zip (runS sps1 is1) (runS sps2 is2)}
--{-
assert Separation2 =
  All sps1a . All sps1b . All sps2a . All sps2b .
  {(sps1a>*<sps1b)-<-(sps2a>*<sps2b)}===
  {(sps1a-<-sps2a)>*<(sps1b-<-sps2b)}
--}

assert Separation3 =
  All sps1 . All sps2 . All is .
  {split (runS (sps1>+<sps2) is)} ===
    {(runS sps1 (lefts is),runS sps2 (rights is))}

split zs = (lefts zs,rights zs)
lefts [] = []
lefts (Left x:zs) = x : lefts zs
lefts (Right _:zs) = lefts zs
rights [] = []
rights (Left _:zs) = rights zs
rights (Right x:zs) = x : rights zs
