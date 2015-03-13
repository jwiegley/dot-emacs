-----------------------------------------------------------------------------
-- |
-- Module      :  PwPfConversion
-- Copyright   :  (c) Jose Proenca 2005
-- License     :  GPL
--
-- Maintainer  :  jproenca@di.uminho.pt
-- Stability   :  experimental
-- Portability :  portable
--
-- Translations between pointwise and point-free expressions, expressed in
--  the modules "PWCore" and "PointFree".
--
-----------------------------------------------------------------------------

module PwPfConversion (
  -- * Translation from "Pointfree" to "PWCore"
  pf2core,

  -- * Translation from "PWCore" to "Pointfree"
  core2Pf
) where

import PWCore
import Pointfree


{- | Applies a simple transformation from a 'PFTerm' to a 'PWTerm', in an automated manner.
-}

pf2core :: PFTerm -> PWTerm
pf2core BANG          = Abstr "x" Unit
pf2core ID            = Abstr "x" (Var' "x")
pf2core APP           = Abstr "x" ((Fst $ Var'"x") :@:
                                 (Snd $ Var' "x"))
pf2core (Curry t1)    = Abstr "x" (Abstr "y" 
                        ((pf2core t1):@:((Var' "y"):><:(Var' "x"))) )
pf2core (t1 :.: t2)   = Abstr "x" ((pf2core t1):@:((pf2core t2):@:(Var' "x")))
pf2core (t1 :\/: t2)  = Abstr "x" (Case (Var' "x") 
                        ("y" , (pf2core t1):@:(Var' "y")) 
                        ("z" , (pf2core t2):@:(Var' "z")))
pf2core (t1 :/\: t2)  = Abstr "x" ((pf2core t1):><:(pf2core t2))
pf2core FST           = Abstr "x" (Fst $ Var' "x")
pf2core SND           = Abstr "x" (Snd $ Var' "x")
pf2core INL           = Abstr "x" (Inl $ Var' "x")
pf2core INR           = Abstr "x" (Inr $ Var' "x")
pf2core (IN  str)     = Abstr "x" (In  str  $ Var' "x")
pf2core (OUT str)     = Abstr "x" (Out str $ Var' "x")
pf2core FIX           = Abstr "x" (Fix $ Var' "x")
pf2core (Macro x)     = Var' x


-- | A context will be a left-nested pair, where the most to the
--   right value will be a never used constant
type Context = PWTerm


-- | Calculates a "path" to a variable in a context by composing the
--   "fst" and "snd" functions
path :: Context -> PWTerm -> PFTerm
path (t:><:(Var' y)) (Var' x)
     | x == y    = SND
     | otherwise = (path t (Var' x)) :.: FST
path _ (Var' x) = Macro x



-- | Given a Context, it calculates the translation from Core
--   to Point-free
core2pf :: Context -> PWTerm -> PFTerm


{- | Applies the conversion of a pointwise expression of type @A@  and obtains
     a pointfree expression of type @1->A@, to which is applied a poinfree macro
     to get the correct type again.
-}
-- (unpnt f = app . (f . bang /\ id))
core2Pf :: PWTerm -> PFTerm
core2Pf t = APP :.: (((core2pf Unit t) :.: BANG) :/\: ID)


-- paramorphisms for Int
core2pf cont ((((Fix (Abstr r1 (Abstr n1 (Abstr f1 (Abstr z1 
    (Case (Out typ (Var' n2))
         (_,Var' z2)
         (y1,(Var' f2 :@: Var' y2) :@: (((Var' r2 :@: Var' y3) :@: Var' f3)
          :@: Var' z3)))))))) :@: n) :@: f) :@: z)
  | r1==r2 && n1==n2 && f1==f2 && f2==f3 &&
    z1==z2 && z2==z3 && y1==y2 && y2==y3 &&
    isClosed f && isClosed z =
       (PARA typ (unpoint $ g(f,z))) :.: (core2pf cont n)
 where
    unpoint f = APP :.: ((f :.: BANG) :/\: ID) 
    g (f,z) = let y = getFV f; x = getFV (z:><:Var' y)
            in core2pf Unit $
     Abstr x $
       Case (Var' x) ("_",z)
                      (y,f :@: (Snd$Var' y) :@: (Fst$Var' y))
----------------------------- pred ^ - recursive result ^

-- paramorphisms for [a]
core2pf cont ((((Fix (Abstr r1 (Abstr l1 (Abstr f1 (Abstr z1 
    (Case (Out typ (Var' l2))
         (_,Var' z2)
         (y1,Var' f2 :@: (Fst (Var' y2)) :@: (Snd (Var' y3)) :@:
            (Var' r2 :@: (Snd (Var' y4)) :@: Var' f3 :@: Var' z3))))))))
         :@: n) :@: f) :@: z)
  | r1==r2 && l1==l2 && f1==f2 && f2==f3 &&
    z1==z2 && z2==z3 && y1==y2 && y2==y3 && y3==y4 &&
    isClosed f && isClosed z =
       (PARA typ (unpoint $ g(f,z))) :.: (core2pf cont n)
 where
    unpoint f = APP :.: ((f :.: BANG) :/\: ID) 
    g (f,z) = let y = getFV f; x = getFV (z:><:Var' y)
            in core2pf Unit $
     Abstr x $
       Case (Var' x) ("_",z)
              (y,f :@: (Fst$Var' y) :@: (Snd$Snd$Var' y) :@: (Fst$Snd$Var' y))
------------------------- head ^  --------- tail ^ --- recursive result ^


core2pf _    Unit        = BANG
core2pf cont var@(Var' x) = path cont var
core2pf cont (t1:><:t2)  = (core2pf cont t1):/\:(core2pf cont t2)
core2pf cont (Fst t)     = FST :.: (core2pf cont t)
core2pf cont (Snd t)     = SND :.: (core2pf cont t)
core2pf cont (Abstr x t) = Curry (core2pf (cont:><:(Var' x)) t)
core2pf cont (t1:@:t2)   = APP :.: ((core2pf cont t1):/\:(core2pf cont t2))
core2pf cont (Inl t)     = INL :.: (core2pf cont t)
core2pf cont (Inr t)     = INR :.: (core2pf cont t)
core2pf cont (Case t (x,u) (y,v)) = 
    APP :.: ((Curry (((core2pf (cont:><:(Var' x)) u) :\/: 
            (core2pf (cont:><:(Var' y)) v)) :.: (Macro "distr")))
            :/\: (core2pf cont t))
core2pf cont (In  str t) = IN  str :.: (core2pf cont t)
core2pf cont (Out str t) = OUT str :.: (core2pf cont t)
core2pf cont (Fix t)    = FIX :.: (core2pf cont t)


-- get the free variables
getFV :: PWTerm -> String
getFV = (\x->x++"_").maximum.getVars

getVars :: PWTerm -> [String]
getVars (Var' str)      = [str]
getVars Unit           = []
getVars (t1:><:t2)     = (getVars t1) ++ (getVars t2)
getVars (Abstr str t)  = str:(getVars t)
getVars (t1:@:t2)      = (getVars t1) ++ (getVars t2)
getVars (Case t1 (str1,t2) (str2,t3)) =
        str1:str2:(getVars t1++getVars t2++getVars t3)
getVars (Fst t)   = getVars t
getVars (Snd t)   = getVars t
getVars (Inl t)   = getVars t
getVars (Inr t)   = getVars t
getVars (In _ t)  = getVars t
getVars (Out _ t) = getVars t
getVars (Fix t)   = getVars t


isClosed :: PWTerm -> Bool
isClosed t = closed t []
 where
  closed Unit _           = True
  closed (Var' str) ac     = str `elem` ac
  closed (t1:><:t2) ac    = (closed t1 ac) && (closed t2 ac)
  closed (Abstr str t) ac = closed t (str:ac)
  closed (t1:@:t2) ac     = (closed t1 ac) && (closed t2 ac)
  closed (Case t1 (str1,t2) (str2,t3)) ac =
     (closed t1 ac) && (closed t2 (str1:ac)) && (closed t3 (str2:ac))
  closed (Fst t) ac       = closed t ac
  closed (Snd t) ac       = closed t ac
  closed (Inl t) ac       = closed t ac
  closed (Inr t) ac       = closed t ac
  closed (In _ t) ac      = closed t ac
  closed (Out _ t) ac     = closed t ac
  closed (Fix t) ac       = closed t ac
