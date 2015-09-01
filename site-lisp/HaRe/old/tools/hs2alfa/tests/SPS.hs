-- Synchronous stream processors
module SPS where

newtype S i o = S (i->(o,S i o))
feed (S sps) i = sps i


runS _       []     = []
runS sps (i:is) = continue (feed sps i) is
continue c is = fst c:runS (snd c) is

mapS f = S sps
  where sps i = (f i,S sps)

mapAccumS f s0 = S (sps s0)
  where
    sps s1 i = case f s1 i of
                (s2,o) -> (o,S (sps s2))

--(>*<) :: S i1 o1 -> S i2 o2 -> S (i1,i2) (o1,o2)
sps1 >*< sps2 = S sps
  where
    sps (i1,i2) = ((fst o1,fst o2),snd o1>*<snd o2)
       where o1 = feed sps1 i1
	     o2 = feed sps2 i2

(>+<) :: S i1 o1 -> S i2 o2 -> S (Either i1 i2) (Either o1 o2)
sps1 >+< sps2 = S sps
  where
    sps (Left  i1) = (Left  o1,sps1'>+<sps2) where (o1,sps1') = feed sps1 i1
    sps (Right i2) = (Right o2,sps1>+<sps2') where (o2,sps2') = feed sps2 i2

sps1 -<- sps2 = S sps
  where
    sps i2 = (o1,sps1'-<-sps2')
     where
       (o2,sps2') = feed sps2 i2
       (o1,sps1') = feed sps1 o2

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
lefts zs = [x|Left x<-zs]
rights zs = [y|Right y<-zs]
