{-+
Knot-tying definitions for the base+property syntax to Isabelle translation.
-}

module Prop2Isabelle where
import BaseStruct2Isabelle(transP,transD,transE,transT,transTp,transTa,transId,transQ)
import PropStruct2Isabelle(transPD,transPA,transPP)
import PropSyntax
import IsabelleAST

combine :: IsaDecl -> IsaDecl -> IsaDecl
combine (IsaDomain (DomainDecl xs))
        (IsaDomain (DomainDecl ys)) = IsaDomain (DomainDecl (xs ++ ys))
combine (IsaFixrec (FixrecDecl xs))
        (IsaFixrec (FixrecDecl ys)) = IsaFixrec (FixrecDecl (xs ++ ys))
combine _ _ = error "Illegal mutual recursion"

combineDecls :: [IsaDecl] -> IsaDecl
combineDecls = foldr1 combine

fixrec2consts :: [(String,Type)] -> FixrecDecl -> ConstsDecl
fixrec2consts table (FixrecDecl xs) = ConstsDecl (zipWith TypeSig ns ts)
  where
    typeof n = case lookup n table of Just t -> t
    ns = map head_of_HMatches xs
    ts = map typeof ns

addConstsDecls :: [(String,Type)] -> [IsaDecl] -> [IsaDecl]
addConstsDecls table [] = []
addConstsDecls table (x:xs) = case x of
  IsaFixrec d -> IsaConsts (fixrec2consts table d) : x : addConstsDecls table xs
  _           -> x : addConstsDecls table xs

------------------------------------------------------------

--transPat :: PrintableOp i => HsPatI i -> P
transPat (Pat p) = transP transId transPat p

transDecs ds = map transDec ds

--transDec :: (IsSpecialName i,PrintableOp i) => HsDeclI i -> D
transDec (Dec d) =
    prop (transD transId transExp transPat transLocalDecs transType transContext transTlhs)
         (transPD transId transAssertion transPredicate)
         d

--transExp :: HsExp -> E
transExp (Exp e) =
    transE transId transExp transPat transLocalDecs transType transContext e

transAssertion (PA a) =
    transPA transId transExp transQType transAssertion transPredicate
            a

transPredicate (PP p) =
    transPP transId transExp transPat transQType transAssertion transPredicate
            p

transType (Typ t) = transT transId transType t
transContext ts = undefined -- map transType ts

transQType qt = transQ transContext transType qt

transLocalDecs ds = error "transLocalDecs"

transTlhs (Typ t) = transTp transId transTlhs transTarg t
  where
    transTarg (Typ t) = transTa transId t
