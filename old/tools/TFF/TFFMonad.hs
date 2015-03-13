module TFFMonad where

import Syntax 
import TypesTerms
import Char(chr,ord)

--------------------------------------------------------------------------------
-- The monad
--

type Env        = [(HsName, Term)]
type FreshVars  = (Int, Int, Int)   

tvarCtr (x,_,_) = x
funCtr  (_,x,_) = x
valCtr  (_,_,x) = x

incTvarCtr (x,y,z)  = (x+1, y, z)
incFunCtr  (x,y,z)  = (x, y+1, z)
incValCtr  (x,y,z)  = (x, y, z+1)

valName fvs     = UnQual $ 'x' : show (valCtr fvs)
funName fvs     = UnQual $ [chr (funCtr fvs + ord 'f')]
tvarName fvs    = UnQual $ [chr (tvarCtr fvs + ord 'A')]


newtype FM a    = FM ( (FreshVars, Env) -> (a, FreshVars) )

instance Monad FM where
    return x        = FM (\(fvs, e) -> (x, fvs))
    FM f >>= g      = FM bind
        where
        bind (fvs, e) =  
            let (a, fvs')   = f (fvs, e)
                FM h        = g a
            in h (fvs', e)

inExtendedEnv :: HsName -> Term -> FM a -> FM a
inExtendedEnv n t (FM f) = FM (\(fvs, e) -> f (fvs, (n, t):e))

lookUp :: HsName -> FM Term
lookUp n = FM (\(fvs, e) -> (maybe no id (lookup n e), fvs))
    where
    no = error $ "lookUp: " ++ (show n) ++ " not in environment."


newVar :: Type -> FM Term
newVar t = FM f
    where
    f (fvs, e) = if isFun t
        then ( (hsEVar (funName fvs) ,t) , incFunCtr fvs ) 
        else ( (hsEVar (valName fvs) ,t) , incValCtr fvs ) 

newTVar :: FM Type
newTVar = FM f
    where
    f (fvs, e)  = (mkTyVar (tvarName fvs), incTvarCtr fvs)


run :: FM a -> a
run (FM f) = let (v, _) = f ((0,0,0), []) in v


--
--------------------------------------------------------------------------------


