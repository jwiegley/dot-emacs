module HsPropMaps where
import HsPropStruct
import HsIdent

import AccList
import MUtils
import Products((><))

--- Maps -----------------------------------------------------------------------

mapPD :: (i1->i2) -> (pa1->pa2) -> (pp1->pp2) -> PD i1 pa1 pp1 -> PD i2 pa2 pp2
mapPD idf paf ppf pd =
  case pd of
    HsPropDecl s n ns p ->HsPropDecl s (idf n) (map (mapHsIdent idf) ns) (ppf p)
    HsAssertion s optn a->HsAssertion s (idf # optn) (paf a)

mapPP idf = mapPP2 idf idf

mapPP2 :: (i1->i2)->(i1->i2)->(e1->e2)->(p1->p2)
          ->(t1->t2)->(pa1->pa2)->(pp1->pp2)
          -> PP i1 e1 p1 t1 pa1 pp1 -> PP i2 e2 p2 t2 pa2 pp2
mapPP2 vf cf ef pf tf paf m pp =
  case pp of
--  PredId i -> PredId (cf i)
    PredApp i ts ps -> PredApp (cf i) (map tf ts) (map (mapEither ef m) ps)
    PredArrow p1 p2 -> PredArrow (m p1) (m p2)
    PredInfixApp p1 i p2 -> PredInfixApp (m p1) (cf i) (m p2)
    PredNeg optt p -> PredNeg (tf # optt) (m p)
    PredOp op optt p1 p2 -> PredOp op (tf # optt) (m p1) (m p2)
    PredLfp i optt p -> PredLfp (cf i) (tf # optt) (m p)
    PredGfp i optt p -> PredGfp (cf i) (tf # optt) (m p)
    PredNil -> PredNil
    PredLifted e -> PredLifted (ef e)
    PredStrong p -> PredStrong (m p)
    PredParen p -> PredParen (m p)
    PredComp pts a -> PredComp (map (pf><fmap tf) pts) (paf a)

mapPA idf = mapPA2 idf idf

mapPA2 :: (i1->i2)->(i1->i2)->(e1->e2)->(t1->t2)->(pa1->pa2)->(pp1->pp2)
           -> PA i1 e1 t1 pa1 pp1 -> PA i2 e2 t2 pa2 pp2
mapPA2 vf cf ef tf m ppf pa =
    case pa of
      Quant q i optt pa -> Quant q (vf i) (tf # optt) (m pa)
--    PropId i -> PropId (cf i)
      PropApp i ts ps -> PropApp (cf i) (map tf ts) (map (mapEither ef ppf) ps)
      PropNeg a -> PropNeg (m a)
      PropOp op a1 a2 -> PropOp op (m a1) (m a2)
      PropEqual e1 e2 -> PropEqual (ef e1) (ef e2)
      PropHas e p -> PropHas (ef e) (ppf p)
      PropParen a -> PropParen (m a)
--    PropLambda i a -> PropLambda (vf i) (m a)
--    PropLet i optt e a -> PropLet (vf i) (tf # optt) (ef e) (m a)

--- Accumulators ---------------------------------------------------------------

type Acc i b = i->b->b

accPD :: Acc i b->Acc pa b->Acc pp b->Acc (PD i pa pp) b
accPD idf paf ppf pd =
  case pd of
    HsPropDecl s n ns p  -> idf n . accList (accHsIdent idf) ns . ppf p
    HsAssertion s optn a -> maybe id idf optn . paf a

accPP :: Acc i b->Acc e b->Acc p b->Acc t b->Acc pa b->Acc pp b->Acc (PP i e p t pa pp) b
accPP idf ef pf tf paf ppf pp =
  case pp of
--  PredId i -> idf i
    PredApp i ts as -> idf i . accList tf ts . accList (either ef ppf) as
    PredArrow pp1 pp2 -> ppf pp1 . ppf pp2
    PredInfixApp pp1 i pp2 -> ppf pp1 . idf i . ppf pp2
    PredNeg optt p -> maybe id tf optt . ppf p
    PredOp op optt p1 p2 -> maybe id tf optt . ppf p1 . ppf p2
    PredLfp i optt pp -> idf i . maybe id tf optt . ppf pp
    PredGfp i optt pp -> idf i . maybe id tf optt . ppf pp
    PredNil -> id
    PredLifted e -> ef e
    PredStrong pp -> ppf pp
    PredComp pts pa -> accList accComp pts . paf pa
    PredParen pp  -> ppf pp
  where
    accComp (p,optt) = pf p . maybe id tf optt

accPA :: Acc i b->Acc e b->Acc t b->Acc pa b->Acc pp b->Acc (PA i e t pa pp) b
accPA idf ef tf paf ppf pa =
    case pa of
      Quant q i optt pa -> idf i . maybe id tf optt . paf pa
--    PropId i -> idf i
      PropApp i ts es -> idf i . accList tf ts . accList (either ef ppf) es
      PropNeg a -> paf a
      PropOp op a1 a2 -> paf a1 . paf a2
      PropEqual e1 e2 -> ef e1 . ef e2
      PropHas e p -> ef e . ppf p
      PropParen a -> paf a
--    PropLambda i a -> idf i . paf a
--    PropLet i optt e a -> idf i . maybe id tf optt . ef e . paf a

--- Sequencers -----------------------------------------------------------------

seqPD :: (Functor m,Monad m) => PD (m i) (m pa) (m pp) -> m (PD i pa pp)
seqPD pd =
  case pd of
    HsPropDecl  s n ns p -> HsPropDecl s # n <# mapM seqHsIdent ns <# p
    HsAssertion s optn a -> HsAssertion s # seqMaybe optn  <# a

seqPP :: (Functor m,Monad m) => PP (m i) (m e) (m p) (m t) (m pa) (m pp)
          -> m (PP i e p t pa pp)
seqPP pp =
  case pp of
--  PredId i -> PredId # i
    PredApp i ts ps -> PredApp # i <# sequence ts <# mapM seqEither ps
    PredArrow p1 p2 -> PredArrow # p1 <# p2
    PredInfixApp p1 i p2 -> PredInfixApp # p1 <# i <# p2
    PredNeg optt p -> PredNeg # seqMaybe optt <# p
    PredOp op optt p1 p2 -> PredOp op # seqMaybe optt <# p1 <# p2
    PredLfp i optt p -> PredLfp # i <# seqMaybe optt <# p
    PredGfp i optt p -> PredGfp # i <# seqMaybe optt <# p
    PredNil -> return PredNil
    PredLifted e -> PredLifted # e
    PredStrong p -> PredStrong # p
    PredParen p -> PredParen # p
    PredComp pts a -> PredComp # mapM spts pts <# a
      where spts (mp,optmt) = (,) # mp <# seqMaybe optmt

seqPA :: (Functor m,Monad m) => PA (m i) (m e) (m t) (m pa) (m pp)
         -> m (PA i e t pa pp)
seqPA pa =
  case pa of
    Quant q i optt pa -> Quant q # i <# seqMaybe optt <# pa
--  PropId i -> PropId # i
    PropApp i ts ps -> PropApp # i <# sequence ts <# mapM seqEither ps
    PropNeg a -> PropNeg # a
    PropOp op a1 a2 -> PropOp op # a1 <# a2
    PropEqual e1 e2 -> PropEqual # e1 <# e2
    PropHas e p -> PropHas # e <# p
    PropParen a -> PropParen # a
--  PropLambda i a -> PropLambda # i <# a
--  PropLet i optt e a -> PropLet # i <# seqMaybe optt <# e <# a
