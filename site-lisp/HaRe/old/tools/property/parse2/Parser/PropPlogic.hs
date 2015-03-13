module PropPlogic where
import Prelude hiding (pred)
import PropPosSyntax(HsName,HsIdentI(..),HsExp,HsPat,HsQualType,hsPVar,
                     Assertion,Predicate,PredArg,PropOp,Quantifier)
import HasPropStruct
import MUtils
import Monad(mplus)

data Plogic
  = Quant Quantifier HsName (Maybe HsQualType) Plogic
  | App HsName [PredArg HsExp Plogic]
  | InfixApp Plogic HsName Plogic
  | Neg Plogic
  | Op PropOp Plogic Plogic
  | Equal HsExp HsExp
  | Has HsExp Plogic
  | Arrow Plogic Plogic
  | Lfp HsName Plogic
  | Gfp HsName Plogic
  | Nil
  | Lifted HsExp
  | Strong Plogic
  | Comp [(HsPat,Maybe HsQualType)] Plogic
  | Paren Plogic -- preserve parens to rewrite infix apps after parsing

-- A hack to give '->' higher precedence than ':::' in Plogic assertions:
Has e p1 `arrow` p2 = Has e (p1 `Arrow` p2)
p1 `arrow` p2 = p1 `Arrow` p2

plogicAssertion p = prop p

prop :: (Functor m,Monad m) => Plogic -> m Assertion
prop p =
  case p of
    Quant q n optt p -> quant q n optt # prop p
    App n args -> propApp n # plogicArgs args
    Neg p -> propNeg # prop p
    Op op p1 p2 -> propOp op # prop p1 <# prop p2
    Equal e1 e2 -> return (propEqual e1 e2)
    Has e p -> propHas e # pred p
    Paren p -> propParen # prop p
    _ -> fail "Bad Plogic assertion" -- !!!

plogicArgs args = mapM plogicArg args
plogicArg args = either (return . Left) (Right #. pred) args

propDecl loc c xs p = uncurry (hsPropDecl loc c) # pred' xs p

pred' [] p = (,) [] # pred p
pred' args p = ((,) args # pred p) `mplus` pred'' args p
  where 
    pred'' args p =
      do HsVar x <- return (last args)
         (,) (init args) . predComp [(hsPVar x,Nothing)] # prop p

pred :: (Functor m,Monad m) => Plogic -> m Predicate
pred p =
  case p of
    App n args       -> predApp n # plogicArgs args
    Arrow p1 p2      -> predArrow # pred p1 <# pred p2
    InfixApp p1 i p2 -> predInfixApp # pred p1 <# return i <# pred p2
    Neg p            -> predNeg Nothing # pred p
    Op op p1 p2      -> predOp op Nothing # pred p1 <# pred p2
    Lfp i p          -> predLfp i # pred p
    Gfp i p          -> predGfp i # pred p
    Nil              -> return predNil
    Lifted e         -> return (predLifted e)
    Strong p         -> predStrong # pred p
    Comp tps p       -> predComp tps # prop p
    Paren p          -> predParen # pred p
    _                -> fail "Bad Plogic predicate"
