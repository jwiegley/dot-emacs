{-# OPTIONS -fglasgow-exts #-}
{-# LANGUAGE MultiParamTypeClasses, OverlappingInstances, UndecidableInstances, FunctionalDependencies, NoMonomorphismRestriction #-}
module ReAssoc where
import HsAssoc
import HsIdent
import Recursive

{-+
A class for extensible rewriting of infix applications according to operator
precedence and associativity.

Since fixity information follows the scope the binding it refers to,
the rewrite uses an environment, which is extended when entering the
scope of a local definition.
-}

class ReAssoc i e where
  reAssoc :: OperatorEnv (HsIdentI i) -> e -> e

reAssocRec env = mapRec (reAssoc env)

{-+
To be able to reassociate infix operators in an expression type, all we need
is to be able take infix applications apart, and build new ones:
-}
class HasInfixApp i e a | e->a i where
  infixApp   :: a -> HsIdentI i -> a -> e
  isInfixApp :: e -> Maybe (a,HsIdentI i,a)

{-+
We also need to obtain the declared fixities of the operators
-}
class HasInfixDecls i ds | ds->i where
  getInfixDecls :: ds -> OperatorEnv (HsIdentI i)

getInfixDeclsRec x = getInfixDecls (struct x)

{-+
A reusable function that rewrites infix applications. Using this when
defining instances of ReAssoc, all that is left to do is pass the aprropriate
operator environment around.
-}
--property: reAssocOp should work.
--proof: it does the same thing as HsExpUtil.reassociateE.
reAssocOp env e1 op e2 =
    case isInfixApp e1' of
      Nothing -> e'
      Just (e11,op1,e12) ->
	  if p>p1 || p==p1 && a==a1 && a==HsAssocRight
	  then infixApp e11 op1 (reAssoc env (infixApp e12 op e2))
	  else e'
	where
	  HsFixity a p = getFixity env op	      
	  HsFixity a1 p1 = getFixity env op1
  where
    e1' = reAssoc env e1
    e2' = reAssoc env e2
    e' = infixApp e1' op e2'


instance (Eq i,HasInfixDecls i d) => HasInfixDecls i [d] where
  getInfixDecls = foldr (extend2 . getInfixDecls) emptyOE

instance ReAssoc i d => ReAssoc i [d] where reAssoc = map . reAssoc

getInfixes m = oe where OperatorEnv oe = getInfixDecls m
reAssoc' ops = reAssoc (OperatorEnv ops)
