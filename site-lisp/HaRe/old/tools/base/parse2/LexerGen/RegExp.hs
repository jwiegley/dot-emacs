module RegExp where
--import List
import MUtils(usort)

infixl 2 !,-!,:!,:-!
infixr 3 &,:&

{-+ Transitions for transducers: -}
data Trans i o = I i | O o deriving (Show,Eq,Ord)

type Transducer i o = RegExp (Trans i o)

{-+ Regular expressions: -}
data RegExp t
  = One -- the language containing the empty string, unit of :&
  | Zero -- the empty language, unit of :!
  | S t -- a single symbol
  | RegExp t :& RegExp t -- sequence (associative)
  | RegExp t :! RegExp t -- alternative (cummutative and associative)
  | RegExp t :-! RegExp t -- difference
  | Many (RegExp t) -- sequence of zero or more
  | Some (RegExp t) -- sequence of one or more
-- An experimental extension with a fix-point operator:
  | Fix (RegExp t)
  | Self
  deriving (Eq,Ord,Show)

{-+ Some convenient constructor functions: -}
e     = One
z     = Zero
t     = S . I
o     = S . O
ts rs = seqs $ map t rs
a  rs = alts $ map t rs

opt r = r ! e

alts rs = foldr (!) z rs
seqs rs = foldr (&) e rs

{-+ Optimizing regular expression constructors: -}
many One = One
many Zero = One
many (Many r) = Many r
many (Some r) = Many r
many r = Many r

some One = One
some Zero = Zero
some (Many r) = Many r
some (Some r) = Some r
some r = Some r

r1 ! r2   = alts' (usort ts)
  where
    ts = terms r1 . terms r2 $ []

    alts' [] = z
    alts' ts = foldr1 (:!) ts

    terms Zero = id
    terms (r1 :! r2) = terms r1 . terms r2
    terms r = (r:)

r1 & Zero = Zero
r1 & One  = r1
r1 & r2   = consFactors r1 r2
  where
    consFactors One = id
    consFactors Zero = const Zero
    consFactors (r1:&r2) = consFactors r1 . consFactors r2
    consFactors r = (r:&)

Zero -! r = Zero
r -! Zero = r
r1 -! r2 = if r1==r2 then Zero else r1 :-! r2

fix Zero = Zero
fix One = One
fix Self = Zero
fix ((One:!Self):&r) | not (selfIn r) = some r
fix r = if selfIn r then Fix r else r

selfIn r =
     case r of
       Zero -> False
       One -> False
       S _ -> False
       r1 :& r2  -> selfIn r1 || selfIn r2
       r1 :! r2  -> selfIn r1 || selfIn r2
       r1 :-! r2 -> selfIn r1 || selfIn r2
       Many r -> selfIn r
       Some r -> selfIn r
       Fix r -> False
       Self -> True
