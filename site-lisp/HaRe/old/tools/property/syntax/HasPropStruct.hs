module HasPropStruct where
import HsPropStruct

class HasPropStruct rec prop | rec->prop where
  proprec :: prop -> rec

class GetPropStruct rec prop | rec->prop where
  propstruct :: rec -> Maybe prop

hsAssertion loc n a = proprec $ HsAssertion loc n a
hsPropDecl loc n ns p = proprec $ HsPropDecl loc n ns p

quant q i t pa = proprec $ Quant q i t pa
propId i = proprec $ PropApp i [] []
propApp i es = tpropApp i [] es
tpropApp i ts es = proprec $ PropApp i ts es
propNeg pa = proprec $ PropNeg pa
propOp op pa1 pa2 = proprec $ PropOp op pa1 pa2
propConj x = propOp Conj x
propDisj x = propOp Disj x
propEqual e1 e2 = proprec $ PropEqual e1 e2
propHas e pp = proprec $ PropHas e pp
propParen pa = proprec $ PropParen pa
--propLambda i pa = proprec $ PropLambda i pa
--propLet i t e pa = proprec $ PropLet i t e pa

predId i = proprec $ PredApp i [] []
predApp i as = tpredApp i [] as
tpredApp i ts as = proprec $ PredApp i ts as
predArrow pp1 pp2 = proprec $ PredArrow pp1 pp2
predInfixApp pp1 i pp2 = proprec $ PredInfixApp pp1 i pp2
predNeg optt pa = proprec $ PredNeg optt pa
predOp op optt pa1 pa2 = proprec $ PredOp op optt pa1 pa2
predLfp i pp = proprec $ PredLfp i Nothing pp
predGfp i pp = proprec $ PredGfp i Nothing pp
predLfp' i t pp = proprec $ PredLfp i (Just t) pp
predGfp' i t pp = proprec $ PredGfp i (Just t) pp
predNil = proprec PredNil
predLifted e = proprec $ PredLifted e
predStrong pp = proprec $ PredStrong pp
predComp pts pa = proprec $ PredComp pts pa
predParen pp = proprec $ PredParen pp

predNil :: HasPropStruct r (PP i e p t pa pp) => r
