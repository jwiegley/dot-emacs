module QC_combinators where

import qualified Prelude as P (not)
import Prelude hiding (not)
import qualified QuickCheck as QC
import ShowFunctions
--import System(getEnv)
import Maybe(fromMaybe)

import Generators(generators)


-- the type of formulas
data F              = Prop QC.Property | Bool Bool

instance QC.Testable F where
  property (Bool p) = QC.property p
  property (Prop p) = p

-- predicates
type Pred a         = a -> F


(/\), (\/), (==>)   :: F -> F -> F
not                 :: F -> F
forAll, exists      :: (Show a, QC.Arbitrary a) => String -> (a -> F) -> F
true,false          :: F

(!)                 :: (a -> Bool) -> Pred a
lfp,gfp             :: (Pred a -> Pred a) -> Pred a
(===)               :: Eq a => a -> a -> F

(-=>)               :: (Show a, QC.Arbitrary a) => Pred a -> Pred b -> Pred (a -> b)

(%:)                :: Pred a -> Pred [a] -> Pred [a]




Bool p /\ Bool q    = Bool (p && q)
_ /\ _              = noNest

Bool p \/ Bool q    = Bool (p || q) 
_ \/ _              = noNest

not (Bool p)        = Bool (P.not p)
not _               = noNest

---
pNot p  = lift1 not p
(^/\) p q = liftPropOp (/\) p q
(^\/) p q = liftPropOp (\/) p q
(^==>) p q = liftPropOp (==>) p q
-- (^<==>) = liftPropOp (<==>)

class LiftProp p where
  lift1 :: (F->F)->p->p
  liftPropOp :: (F->F->F)->p->p->p

instance LiftProp F where
  lift1 = id
  liftPropOp = id

instance LiftProp p => LiftProp (a->p) where
  lift1 f p x = lift1 f (p x)
  liftPropOp op p q x = liftPropOp op (p x) (q x)

--liftPropOp op p q x = p x `op` q x -- The S combinator, missing from Prelude!

---

forAll x f          = Prop (QC.forAll (genFor x) f)

exists              = noExists        -- does not exist :-)

true                = Bool True

false               = Bool False

Bool p ==> q        = Prop (p QC.==> q)
p ==> q             = not p \/ q

x === y             = Bool (x == y)

(p -=> q) f         = forAll "x" $ \x -> p x ==> q (f x)        -- how to control this x

(!) p               = Bool . p


(p %: q) (x:xs)     = p x /\ q xs
(p %: q) _          = false


noNest              = error "nested quantifers are not supported"
noExists            = error "existential quantifiers are not supported"


-- TODO: parametrize on 50
-- lfp f x             = foldr (\/) false $ take 50 $ map ($ x) $ iterate f (const false)
-- gfp f x             = foldr (/\) true  $ take 50 $ map ($ x) $ iterate f (const true)


lfp f               = iterate f (const false) !! 50
--lfp f               = f (lfp f)
gfp f x             = foldr1 (/\) $ take 50 $ map ($ x) $ iterate f (const true)


genFor x            = fromMaybe QC.arbitrary (lookup x generators)


--testToFile fileName f = ...

testToStdout maxTest maxFail verbose =
    QC.check config{QC.configMaxTest=maxTest,QC.configMaxFail=maxFail}
  where 
    config = if verbose then qcVerbose else qcConfig

-- Copied from QuickCheck since they aren't exported:
qcConfig = QC.Config
  { QC.configMaxTest = 100
  , QC.configMaxFail = 1000
  , QC.configSize    = (+ 3) . (`div` 2)
  , QC.configEvery   = \n args -> let s = show n in s ++ [ '\b' | _ <- s ]
  }
         
qcVerbose = qcConfig
  { QC.configEvery = \n args -> show n ++ ":\n" ++ unlines args
  }
