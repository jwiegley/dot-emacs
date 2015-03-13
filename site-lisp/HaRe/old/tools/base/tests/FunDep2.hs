module FunDep2 where
import FunDep 

--instance C (a,Int) a where f = fst

--instance C (Int,b) b where f = snd

instance (C a d,C d c)  => C (a,b) (a,b,c) where f (x,y) = (x,y,f (f x))

--instance C a c => C (a,b) (a,b,c)

g x = f (x, x)

bla = g False

class QualNames qn m n | qn -> m n, m n -> qn where
  getQualifier  :: qn -> Maybe m
  getQualified  :: qn -> n
  mkUnqual      :: n -> qn
  mkQual        :: m -> n -> qn

class HasBaseName ie ib | ie->ib           where getBaseName :: ie -> ib

bq n =  getQualifier (getBaseName n)

newtype M = M String
newtype Id = Id String
data Q = Q M Id | U Id

data PN i = PN i

instance Functor PN where fmap f (PN x) = PN (f x)

instance HasBaseName (PN i) i where getBaseName (PN i) = i

instance QualNames Q M Id where
  getQualifier (Q m x) = Just m
  getQualifier _       = Nothing
  getQualified (Q m x) = x
  getQualified (U   x) = x
  mkUnqual x = U x
  mkQual q x = Q q x

instance QualNames qn m n => QualNames (PN qn) m (PN n) where
    getQualifier                = bq
    getQualified                = fmap getQualified

    mkUnqual                    = fmap mkUnqual
    mkQual m                    = fmap (mkQual m)

bla2 :: QualNames q m n => PN q -> Maybe m
bla2 x = bq x
