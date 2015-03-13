module Preds where

import Syntax hiding (lookUp)
import PrettyPrint

import TFFMonad
import TypesTerms


--------------------------------------------------------------------------------
-- Theorems
--

data Pred
    = Term := Term 
    | Pred :=> Pred 
    | Pred :/\ Pred 
    | Forall Term Pred              -- Term should be a Var term
        deriving (Eq,Show)

instance Printable Pred where
    ppi ((t1,_) := (t2,_))  = ppi t1 <+> text "=" <+> ppi t2
    ppi (p :=> q)           = wrap p <+> text "==>" <+> wrap q
    ppi (p :/\ q)           = wrap p <+> text "/\\" <+> wrap q
    ppi (Forall a p)        = text "!" <> ppTerm a <> text "."
                              $$ nest 4 (ppi p)


getRel :: Type -> Term -> Term -> FM Pred
getRel (Type ty) t1 t2
    = case ty of

        HsTyCon n -> return (t1 := t2)

        HsTyFun p q -> do
            { x  <- newVar (dom t1) 
            ; y  <- newVar (dom t2)
            ; r1 <- getRel p x y    
            ; r2 <- getRel q (applyTerm t1 x) (applyTerm t2 y)
            ; return $ Forall x $ Forall y $ r1 :=> r2
            } 


        HsTyVar a -> do
            { f <- lookUp a 
            ; return (t2 := applyTerm f t1)
            }


getRel (TyAll n t) t1 t2 = do
            { x <- newTVar
            ; y <- newTVar
            ; f <- newVar (mkTyFun x y)
            ; p <- inExtendedEnv n f $
                getRel t (applyType t1 x) (applyType t2 y)
            ; return (Forall f p)
            }
--
--------------------------------------------------------------------------------





