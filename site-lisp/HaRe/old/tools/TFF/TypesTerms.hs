module TypesTerms where

import Syntax
import PrettyPrint


--------------------------------------------------------------------------------
-- Types
-- 

data Type
    = Type (T Type)
    | TyAll HsName Type
        deriving (Show, Eq)

mkTyVar n       = Type $ HsTyVar n
mkTyCon n       = Type $ HsTyCon n
mkTyApp t1 t2   = Type $ HsTyApp t1 t2
mkTyFun t1 t2   = Type $ HsTyFun t1 t2
mkTyTuple ts    = Type $ HsTyTuple ts
mkTyAll n t     = TyAll n t


instance Printable Type where
    ppi (Type t)    = ppi t
    ppi (TyAll n t) = text "forall" <+> ppi n <> text "." $$ nest 4 (ppi t)




isFun :: Type -> Bool
isFun (Type (HsTyFun _ _))      = True
isFun _                         = False


applyType :: Term -> Type -> Term
applyType (term, (TyAll a s)) t = (term, substType t a s) 
applyType _ _                   = error "applyType: to a non-forall type"


substType :: Type -> HsName -> Type -> Type
substType t v ty@(TyAll n x)
    | n == v    = ty
    | otherwise = mkTyAll n (substType t v x)
substType t v ty@(Type (HsTyVar n))
    | n == v    = t
    | otherwise = ty
substType t v (Type s) 
    = Type $ mapT (substType t v) s


--
--------------------------------------------------------------------------------



--------------------------------------------------------------------------------
-- Terms
--

type Term = (HsExp, Type)


dom :: Term -> Type
dom (_, Type (HsTyFun t _)) = t
dom _                       = error "dom: of a non-function term"


applyTerm :: Term -> Term -> Term
applyTerm (s, (Type (HsTyFun dom cdom))) (t, ty)
    | dom == ty     = (hsApp s t, cdom)
    | otherwise     = error $ "applyTerm: wrong types" ++ show dom ++ show ty
applyTerm _ _       = error "applyTerm: applying to non-function"


ppTerm (t,ty)   = ppi t <> text ":" <+> ppi ty

--
--------------------------------------------------------------------------------


