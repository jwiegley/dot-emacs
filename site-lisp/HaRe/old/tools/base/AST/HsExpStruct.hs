{-# LANGUAGE DeriveDataTypeable  #-}
module HsExpStruct where

import SrcLoc1
import HsIdent
import HsLiteral
import HsGuardsStruct(HsAlt)
import HsFieldsStruct

import Data.Generics

-------- Expressions --------------------------------------------------------

data EI i e p ds t c
    = HsId (HsIdentI i) -- collapsing HsVar and HsCon
    | HsLit SrcLoc HsLiteral
    | HsInfixApp e (HsIdentI i) e
    | HsApp e e
    | HsNegApp SrcLoc e
    | HsLambda [p] e
    | HsLet ds e
    | HsIf e e e
    | HsCase e [HsAlt e p ds]
    | HsDo (HsStmt e p ds)
    | HsTuple [e]
    | HsList [e]
    | HsParen e
    | HsLeftSection e (HsIdentI i)
    | HsRightSection (HsIdentI i) e
    | HsRecConstr SrcLoc i (HsFieldsI i e) -- qcon { fbind1, ..., fbindn }
    | HsRecUpdate SrcLoc e (HsFieldsI i e) -- exp_<qcon> { fbind1, ..., fbindn }
    | HsEnumFrom e
    | HsEnumFromTo e e
    | HsEnumFromThen e e
    | HsEnumFromThenTo e  e e
    | HsListComp (HsStmt e p ds)
    | HsExpTypeSig SrcLoc e c t
    --------------------------------
    | HsAsPat i e   -- pattern only
    | HsWildCard         -- ditto
    | HsIrrPat e         -- ditto
      deriving (Read, Show, Data, Typeable, Ord)

instance (Eq i, Eq e, Eq p, Eq ds, Eq t , Eq c) => Eq (EI i e p ds t c) where
  HsId i                == HsId i1                    = i == i1
  HsLit _ l             == HsLit _ l1                 = l == l1
  HsInfixApp x op z     == HsInfixApp x1 op1 z1       = x==x1  && op == op1 && z == z1
  HsApp x y             == HsApp x1 y1                = x == x1 && y == y1
  HsNegApp _ x          == HsNegApp _ x1              = x == x1
  HsLambda ps e         == HsLambda ps1 e1            = ps ==ps1 && e == e1
  HsLet ds e            == HsLet ds1 e1               = ds == ds1 && e == e1
  HsIf x y z            == HsIf x1 y1 z1              = x==x1 && y==y1 && z==z1
  HsCase e alts         == HsCase e1 alts1            = e == e1 && alts == alts1
  HsDo stmts            == HsDo stmts1                = stmts == stmts1
  HsTuple xs            == HsTuple xs1                = xs == xs1
  HsList xs             == HsList xs1                 = xs == xs1
  HsParen x             == HsParen x1                 = x == x1
  HsLeftSection x op    == HsLeftSection x1 op1       = x == x1 && op == op1
  HsRightSection op y   == HsRightSection op1 y1      = op == op1 && y == y1
  HsRecConstr _ n upds    == HsRecConstr _ n1 upds1       = n == n1 && upds == upds1
  HsRecUpdate _ e upds    == HsRecUpdate _ e1 upds1       = e == e1 && upds == upds1
  HsEnumFrom x          == HsEnumFrom x1              = x == x1
  HsEnumFromTo x y      == HsEnumFromTo x1 y1         = x == x1 && y==y1
  HsEnumFromThen x y    == HsEnumFromThen x1 y1       = x == x1 && y==y1
  HsEnumFromThenTo x y z== HsEnumFromThenTo x1 y1 z1  = x == x1 && y==y1 && z==z1
  HsListComp stmts      == HsListComp stmts1          = stmts == stmts1
  HsExpTypeSig _ e c t  == HsExpTypeSig _ e1 c1 t1    = e == e1 && c == c1 && t == t1
  HsAsPat n e           == HsAsPat n1 e1              = n == n1 && e == e1
  HsWildCard            == HsWildCard                 = True
  HsIrrPat e            == HsIrrPat e1                = e == e1
  _                     == _                          = False
 
data HsStmt e p ds
    = HsGenerator SrcLoc p e (HsStmt e p ds)
    | HsQualifier e (HsStmt e p ds)
    | HsLetStmt ds (HsStmt e p ds)
    | HsLast e
      deriving (Ord,Read, Eq, Show, Data, Typeable) 


