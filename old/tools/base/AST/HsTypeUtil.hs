module HsTypeUtil where
import HsTypeStruct

matchT tx ty =
    case (tx, ty) of
    (HsTyFun x1 x2, HsTyFun y1 y2)       -> Just [(x1, y1), (x2, y2)]
--  (HsTyTuple xs, HsTyTuple ys) | length xs == length ys -> Just $ zip xs ys
    (HsTyApp f x, HsTyApp g y)           -> Just [(f, g), (x, y)]
    (HsTyVar n1, HsTyVar n2) | n1 == n2  -> Just []
    (HsTyCon n1, HsTyCon n2) | n1 == n2  -> Just []
    (HsTyForall vs1 ps1 t1,HsTyForall vs2 ps2 t2) | vs1==vs2 && ps1==ps2 -> Just [(t1,t2)] -- hmm
    _                                    -> Nothing

{-
lookupHSNameInType :: TI i t -> Maybe i
lookupHSNameInType (HsTyVar n) = Just n
lookupHSNameInType (HsTyCon n) = Just n
lookupHSNameInType _           = Nothing
-}

{-
tupleToContext make t =
  case t of
    HsTyTuple ts -> ts
    _            -> [make t]
-}


{-
tyVar2id (HsTyVar x) = x
tyVar2id _           = error "tyVar2id: not a type variable."
-}
