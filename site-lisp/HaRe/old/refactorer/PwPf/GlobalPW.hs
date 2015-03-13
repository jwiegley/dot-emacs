-----------------------------------------------------------------------------
-- |
-- Module      :  GlobalPW
-- Copyright   :  (c) Jose Proenca 2005
-- License     :  GPL
--
-- Maintainer  :  jproenca@di.uminho.pt
-- Stability   :  experimental
-- Portability :  portable
--
-- A global pointwise syntax and its relation with:
--
--   * An expression in programatica's abstract syntax tree;
--
--   * A pointwise core - "PWCore".
--
-----------------------------------------------------------------------------

module GlobalPW (
    -- * Data Type
    {-| Represents a pointwise language that:

            (1) is very similar to the way we are used to program in haskell;

            (2) not the most general one, since it only deals with booleans, natural numbers and lists.
    -}
    GLTerm (..),

    -- * Conversion of an haskell expression to a GlobalPW term
    exp2Global,
    
    -- * Conversion of a GlobalPW term to a "PWCore" term
    global2core

 ) where

import PWCore
import RefacUtils
import PrettyPrint

--------------------------------
----- Global definition --------
--------------------------------

data GLTerm 
  = Star                  -- ^Unit
  | V String              -- ^Variable
  | GLTerm:-:GLTerm       -- ^Aplication
  | Lam String GLTerm     -- ^Abstraction
  | GLTerm:&:GLTerm       -- ^Pair
  | Pi1 GLTerm            -- ^Point-wise first
  | Pi2 GLTerm            -- ^Point-wise second
  | Inl' GLTerm           -- ^Point-wise left injection
  | Inr' GLTerm           -- ^Point-wise right injection
  | Case' GLTerm (String,GLTerm) (String,GLTerm)
                          -- ^Case of
  | In'  HsExpP GLTerm    -- ^Injection on a specified type
  | Out' HsExpP GLTerm    -- ^Extraction of the functor of a specified type
  | Fix' GLTerm           -- ^Fixed-point
---------------- from PCF ---------------------
  | T'                    -- ^Constant True
  | F'                    -- ^Constant False
  | Z'                    -- ^Constant Zero
  | Suc GLTerm            -- ^Successor
  | Pred GLTerm           -- ^Predecessor
  | IsZ GLTerm            -- ^is zero?
  | Ite GLTerm GLTerm GLTerm -- ^if then else
  | N'                    -- ^Empty list
  | GLTerm ::: GLTerm     -- ^Constructor for lists
  | Hd GLTerm             -- ^Head of a list
  | Tl GLTerm             -- ^Tail of a list
  | IsN  GLTerm           -- ^is the list empty?
  | Letrec String GLTerm GLTerm
                          -- ^recursive let
---------------- from BNL ---------------------
  | RecNat  GLTerm GLTerm GLTerm
                       -- ^Primitive recursion on Nat's
  | RecList GLTerm GLTerm GLTerm
                       -- ^Primitive recursion on List's
    deriving Show





{- | Applies a simple transformation from an expression of programatica's
     abstract syntax tree to 'GLTerm'.

     The recognized grammar is:
       
      [G, G1, G2, G3 @::=@]
           (G) | @undefined@ | @()@ | @_L@ | @inN (_L::@/type/@) @G |@ ouT (_L::@/type/@)@ 
           |@ True @|@ False @|@ 0 @|@ [] @|@ /n, n>0/ @|@ [@G1@, @G2@, ... ] @| G1@ : @G2 |@ succ @G |@ pred @G
           |@ (==0) @G |@ @G@ == 0 @|@ head @G@ @|@ tail @G@ @|@ null @
           |@ recNat @G1@ @G2@ @G3@ @|@ recList @G1@ @G2@ @G3
           |@ fix @G@ @|@ if @G1@ then @G2@ else @G3@ @|@ /var/ @|@ (@G1@,@G2@) @|@ fst @|@ snd @|@ Left @|@ Right @
           |@ @G1@ /infixOp/ @G2@ @|@ \\/var1 var2 .../ -> @G
           |@ case @G1@ of Left /var1/ -> @G2@; Right /var2/ ->@G3 
           |@ let /var/ = @G1@ in @G2@ 
           @ 

     where types are read as the pretty print string, and /var/, /var1/ and /var2/ are variables that are read as strings also.
-}

exp2Global :: Monad m => HsExpI PNT -> m GLTerm

-- parentisis
exp2Global (Exp (HsParen e)) = exp2Global e

-- unit -> "()" or "undefined" or "_L"
exp2Global (Exp (HsId (HsCon (PNT (PN (Qual (PlainModule "Prelude") "()") (G (PlainModule "Prelude") "()" (N (Just _)))) (ConstrOf (PN "()" (G (PlainModule "Prelude") "()" (N (Just _)))) (TypeInfo {defType = Just Data, constructors = [ConInfo {conName = PN "()" (G (PlainModule "Prelude") "()" (N (Just _))), conArity = 0, conFields = Nothing}], fields = []})) (N (Just loc))))))
    = return Star 

exp2Global (Exp (HsId (HsVar (PNT (PN (UnQual "undefined") (G (PlainModule "Prelude") "undefined" (N (Just _)))) _ (N (Just _))))))
    = return Star

exp2Global (Exp (HsId (HsVar (PNT (PN (UnQual "_L") _) _ _))))
    = return Star


-- Constants (inN,ouT, True, False,[],int)
-- inN (_L::typ) exp
exp2Global (Exp (HsApp (Exp (HsApp (Exp (HsId (HsVar (PNT (PN (UnQual "inN") _) _ (N (Just _)))))) (Exp (HsParen typ@(Exp (HsExpTypeSig _ (Exp (HsId (HsVar (PNT (PN (UnQual "_L") _) _ (N (Just _)))))) [] 
  typ'
  )))))) exp2))
   = exp2Global exp2 >>= return . In' typ--(pp typ)

-- ouT (_L::typ) exp
exp2Global (Exp (HsApp (Exp (HsApp (Exp (HsId (HsVar (PNT (PN (UnQual "ouT") _) _ (N (Just _)))))) (Exp (HsParen typ@(Exp (HsExpTypeSig _ (Exp (HsId (HsVar (PNT (PN (UnQual "_L") _) _ (N (Just _)))))) [] 
  typ'
  )))))) exp2))
   = exp2Global exp2 >>= return . Out' typ --(pp typ)

-- True
exp2Global (Exp (HsId (HsCon (PNT (PN (UnQual "True") (G (PlainModule "Prelude") "True" (N (Just _)))) (ConstrOf (PN "Bool" (G (PlainModule "Prelude") "Bool" (N (Just _)))) (TypeInfo {defType = Just Data, constructors = [ConInfo {conName = PN "False" (G (PlainModule "Prelude") "False" (N (Just _))), conArity = 0, conFields = Nothing},ConInfo {conName = PN "True" (G (PlainModule "Prelude") "True" (N (Just _))), conArity = 0, conFields = Nothing}], fields = []})) (N (Just _))))))
    = return T'

-- False
exp2Global (Exp (HsId (HsCon (PNT (PN (UnQual "False") (G (PlainModule "Prelude") "False" (N (Just _)))) (ConstrOf (PN "Bool" (G (PlainModule "Prelude") "Bool" (N (Just _)))) (TypeInfo {defType = Just Data, constructors = [ConInfo {conName = PN "False" (G (PlainModule "Prelude") "False" (N (Just _))), conArity = 0, conFields = Nothing},ConInfo {conName = PN "True" (G (PlainModule "Prelude") "True" (N (Just _))), conArity = 0, conFields = Nothing}], fields = []})) (N (Just _))))))
    = return F'

-- Zero
exp2Global (Exp (HsLit _ (HsInt 0)))
    = return Z'

-- []
exp2Global ((Exp (HsList [])))
   = return N'

-- n>0
exp2Global (Exp (HsLit _ (HsInt n)))
   | n > 0 = exp2Global (Exp $ HsLit loc0 $ HsInt  (n-1)) >>= return . Suc


------ recursion
-- recNat
exp2Global (Exp (HsApp (Exp (HsApp (Exp (HsApp (Exp (HsId (HsVar (PNT (PN (UnQual "recNat") _) _ _)))) exp1)) exp2)) exp3))
  = do term1 <- exp2Global exp1
       term2 <- exp2Global exp2
       term3 <- exp2Global exp3
       return $ RecNat term1 term2 term3

-- recList
exp2Global (Exp (HsApp (Exp (HsApp (Exp (HsApp (Exp (HsId (HsVar (PNT (PN (UnQual "recList") _) _ _)))) exp1)) exp2)) exp3))
  = do term1 <- exp2Global exp1
       term2 <- exp2Global exp2
       term3 <- exp2Global exp3
       return $ RecList term1 term2 term3

-- fix exp
exp2Global (Exp (HsApp (Exp (HsId (HsVar (PNT (PN (UnQual "fix") _) _ _)))) exp))
    = do term1 <- exp2Global exp
         return $ Fix' term1

-- let var = exp1 -> exp2
exp2Global (Exp (HsLet [Dec (HsPatBind _ (Pat (HsPId (HsVar (PNT (PN (UnQual str) _) _ _)))) (HsBody exp1) [])] exp2))
    =   do t1 <- exp2Global exp1
           t2 <- exp2Global exp2
           return $ Letrec str t1 t2

------ remaining operators
-- succ exp
exp2Global (Exp (HsApp (Exp (HsId (HsVar (PNT (PN (UnQual "succ") _) _ (N (Just _)))))) e))
    = do t <- exp2Global e
         return $ Suc t

-- pred exp
exp2Global (Exp (HsApp (Exp (HsId (HsVar (PNT (PN (UnQual "pred") _) _ (N (Just _)))))) e))
    = do t <- exp2Global e
         return $ Pred t

-- (== 0) exp
exp2Global (Exp (HsApp (Exp (HsRightSection (HsVar (PNT (PN (UnQual "==") (G (PlainModule "Prelude") "==" (N (Just _)))) (MethodOf (PN "Eq" (G (PlainModule "Prelude") "Eq" (N (Just _)))) _ [PN "==" (G (PlainModule "Prelude") "==" (N (Just _))),PN "/=" (G (PlainModule "Prelude") "/=" (N (Just _)))]) _)) (Exp (HsLit _ (HsInt 0))))) exp))
    = do t <- exp2Global exp
         return $ IsZ t

-- exp == 0
exp2Global (Exp (HsInfixApp exp (HsVar (PNT (PN (UnQual "==") (G (PlainModule "Prelude") "==" (N (Just _)))) (MethodOf (PN "Eq" (G (PlainModule "Prelude") "Eq" (N (Just _)))) _ [PN "==" (G (PlainModule "Prelude") "==" (N (Just _))),PN "/=" (G (PlainModule "Prelude") "/=" (N (Just _)))]) (N (Just _)))) (Exp (HsLit _ (HsInt 0)))))
    = do t <- exp2Global exp
         return $ IsZ t

-- [exp1, exp2, ... ]
exp2Global (Exp (HsList (e1:e2)))
  = do t1 <- exp2Global e1
       t2 <- exp2Global (Exp (HsList e2))
       return $ t1 ::: t2

-- x : xs
exp2Global (Exp (HsInfixApp e1 (HsCon (PNT (PN (UnQual ":") (G (PlainModule "Prelude") ":" (N (Just _)))) (ConstrOf (PN "[]" (G (PlainModule "Prelude") "[]" (N (Just _)))) (TypeInfo {defType = Just Data, constructors = [ConInfo {conName = PN "[]" (G (PlainModule "Prelude") "[]" (N (Just _))), conArity = 0, conFields = Nothing},ConInfo {conName = PN ":" (G (PlainModule "Prelude") ":" (N (Just _))), conArity = 2, conFields = Nothing}], fields = []})) (N (Just _)))) e2))
   = do t1 <- exp2Global e1
        t2 <- exp2Global e2
        return $ t1 ::: t2

-- head exp
exp2Global (Exp (HsApp (Exp (HsId (HsVar (PNT (PN (UnQual "head") _) _ (N (Just _)))))) e))
    = do t <- exp2Global e
         return $ Hd t

-- tail exp
exp2Global (Exp (HsApp (Exp (HsId (HsVar (PNT (PN (UnQual "tail") _) _ (N (Just _)))))) e))
    = do t <- exp2Global e
         return $ Tl t

-- null exp
exp2Global (Exp (HsApp (Exp (HsId (HsVar (PNT (PN (UnQual "null") _) _ (N (Just _)))))) e))
    = do t <- exp2Global e
         return $ IsN t

-- if exp1 then exp2 else exp3
exp2Global (Exp (HsIf e1 e2 e3)) =
   do t1 <- exp2Global e1
      t2 <- exp2Global e2
      t3 <- exp2Global e3
      return $ Ite t1 t2 t3

-- var
exp2Global (Exp (HsId (HsVar (PNT (PN (UnQual str) _) _ (N (Just _))))))
   = return $ V str

-- pairs
exp2Global (Exp (HsTuple [e1,e2]))
  = do t1 <- exp2Global e1
       t2 <- exp2Global e2
       return $ t1 :&: t2

-- fst exp
exp2Global (Exp (HsApp (Exp (HsId (HsVar (PNT (PN (UnQual "fst") _) _ (N (Just _)))))) e))
    = do t <- exp2Global e
         return $ Pi1 t

-- snd exp
exp2Global (Exp (HsApp (Exp (HsId (HsVar (PNT (PN (UnQual "snd") _) _ (N (Just _)))))) e))
    = do t <- exp2Global e
         return $ Pi2 t

-- Left exp
exp2Global (Exp (HsApp (Exp (HsId (HsCon (PNT (PN (UnQual "Left") (G (PlainModule "Prelude") "Left" (N (Just _)))) (ConstrOf (PN "Either" (G (PlainModule "Prelude") "Either" (N (Just _)))) (TypeInfo {defType = Just Data, constructors = [ConInfo {conName = PN "Left" (G (PlainModule "Prelude") "Left" (N (Just _))), conArity = 1, conFields = Nothing},ConInfo {conName = PN "Right" (G (PlainModule "Prelude") "Right" (N (Just _))), conArity = 1, conFields = Nothing}], fields = []})) _)))) e))
    = do t <- exp2Global e
         return $ Inl' t

-- Right exp
exp2Global (Exp (HsApp (Exp (HsId (HsCon (PNT (PN (UnQual "Right") (G (PlainModule "Prelude") "Right" (N (Just _)))) (ConstrOf (PN "Either" (G (PlainModule "Prelude") "Either" (N (Just _)))) (TypeInfo {defType = Just Data, constructors = [ConInfo {conName = PN "Left" (G (PlainModule "Prelude") "Left" (N (Just _))), conArity = 1, conFields = Nothing},ConInfo {conName = PN "Right" (G (PlainModule "Prelude") "Right" (N (Just _))), conArity = 1, conFields = Nothing}], fields = []})) _)))) e))
    = do t <- exp2Global e
         return $ Inr' t

-- application
exp2Global (Exp (HsApp e1 e2)) =
   do t1 <- exp2Global e1
      t2 <- exp2Global e2
      return $ t1 :-: t2

-- infix application
exp2Global (Exp (HsInfixApp e1 op e2)) =
   do t1 <- exp2Global e1
      t2 <- exp2Global e2
      return $ (getOpName op) :-: t1 :-: t2
  where getOpName ((HsVar (PNT (PN (UnQual op) _) _ _))) = V op

-- \ var -> exp
exp2Global (Exp (HsLambda [Pat (HsPId (HsVar (PNT (PN (UnQual str) _) _ _)))] e))
   = do t <- exp2Global e
        return $ Lam str t

-- \ var1 var2 ... -> exp
exp2Global (Exp (HsLambda (h@((Pat (HsPId (HsVar _)))):t) e))
    = exp2Global (Exp (HsLambda [h] (Exp (HsLambda t e))))

-- case exp1 of Left var2 -> exp2; Right var3 -> exp3
exp2Global (Exp (HsCase exp1 
             [HsAlt _ (Pat (HsPApp (PNT (PN (UnQual "Left") (G (PlainModule "Prelude") "Left" (N (Just _)))) (ConstrOf (PN "Either" (G (PlainModule "Prelude") "Either" (N (Just _)))) (TypeInfo {defType = Just Data, constructors = [ConInfo {conName = PN "Left" (G (PlainModule "Prelude") "Left" (N (Just _))), conArity = 1, conFields = Nothing},ConInfo {conName = PN "Right" (G (PlainModule "Prelude") "Right" (N (Just _))), conArity = 1, conFields = Nothing}], fields = []})) (N (Just _))) [Pat (HsPId (HsVar (PNT (PN (UnQual str2) _) _ _)))])) (HsBody exp2) []
             ,HsAlt _ (Pat (HsPApp (PNT (PN (UnQual "Right") (G (PlainModule "Prelude") "Right" (N (Just _)))) (ConstrOf (PN "Either" (G (PlainModule "Prelude") "Either" (N (Just _)))) (TypeInfo {defType = Just Data, constructors = [ConInfo {conName = PN "Left" (G (PlainModule "Prelude") "Left" (N (Just _))), conArity = 1, conFields = Nothing},ConInfo {conName = PN "Right" (G (PlainModule "Prelude") "Right" (N (Just _))), conArity = 1, conFields = Nothing}], fields = []})) (N (Just _))) [Pat (HsPId (HsVar (PNT (PN (UnQual str3) _) _ _)))])) (HsBody exp3) []]))
  = do t1 <- exp2Global exp1
       t2 <- exp2Global exp2
       t3 <- exp2Global exp3
       return $ Case' t1 (str2,t2) (str3,t3)

exp2Global x = --mzero
               --fail 
               error $ "not a Global term: "++ pp x




--------------------------------
------- global to core ---------

{- | Converts a 'GLTerm' to a 'PWTerm', which is a more general representation for
       pointwise terms, but with less pratical constructors (in "PWCore").
-}

global2core :: GLTerm -> PWTerm
global2core Star = Unit
global2core (V str) = Var' str
global2core (Lam str t) = Abstr str (global2core t)
global2core (t1 :-: t2) = (global2core t1) :@: (global2core t2)
global2core (t1 :&: t2) = (global2core t1) :><: (global2core t2)
global2core (Pi1 t)     = Fst (global2core t)
global2core (Pi2 t)     = Snd (global2core t)
global2core T'          = In boolT (Inl Unit)
global2core F'          = In boolT (Inr Unit)
global2core Z'          = In intT (Inl Unit)
global2core (Suc t)     = In intT (Inr $ global2core t)
global2core (Pred t)    =
        Case (Out intT$ global2core t) ("_",In intT (Inl Unit))
                          ("x", (Var' "x"))
global2core (IsZ t) =
        Case (Out intT$ global2core t) ("_", In boolT (Inl Unit))
                          ("_", In boolT (Inr Unit))
global2core (Ite t1 t2 t3) =
        Case (Out boolT$ global2core t1) ("_", global2core t2)
                           ("_", global2core t3)
global2core (Fix' t) = Fix (global2core t)

global2core N'          = In listT (Inl Unit)
global2core (t1 ::: t2) = In listT (Inr ((global2core t1):><:(global2core t2)))
global2core (IsN t) =
        Case (Out listT$ global2core t) ("_", In boolT (Inl Unit))
                          ("_", In boolT (Inr Unit))
global2core (Hd t) =
        Case (Out listT$ global2core t) ("_", Var' "undefined")
                          ("x", Fst $ Var' "x")
global2core (Tl t) =
        Case (Out listT$ global2core t) ("_", In listT (Inl Unit))
                          ("x", Snd $ Var' "x")
global2core (Letrec str t1 t2) =
        let func = (Fix (Abstr str (global2core t1)))
        in  (Abstr str (global2core t2)) :@: func
global2core (Inl' t) = Inl (global2core t)
global2core (Inr' t) = Inr (global2core t)
global2core (Case' a (s1,b) (s2,c)) =
   Case (global2core a) (s1,global2core b) (s2,global2core c)
global2core (In' s t) = In s (global2core t)
global2core (Out' s t) = Out s (global2core t)
global2core (RecNat t1 t2 t3) =
        (Fix $ Abstr "r" $ Abstr "n" $ Abstr "f" $ Abstr "z" $
            Case (Out intT (Var' "n"))
                ("x", Var' "z")
                ("y", (Var' "f") :@: (Var' "y") :@:
                    ((Var' "r"):@:(Var' "y"):@:(Var' "f"):@:(Var' "z"))))
        :@: (global2core t1) :@: (global2core t2) :@: (global2core t3)
global2core (RecList t1 t2 t3) =
        (Fix $ Abstr "r" $ Abstr "l" $ Abstr "f" $ Abstr "z" $
            Case (Out listT (Var' "l"))
                ("x", Var' "z")
                ("y", (Var' "f") :@: (Fst$Var' "y") :@: (Snd$Var' "y") :@:
                   ((Var' "r"):@:(Snd$Var' "y"):@:(Var' "f"):@:(Var' "z"))))
        :@: (global2core t1) :@: (global2core t2) :@: (global2core t3)
 

---- expressions for (_L::Int)
--                   (_L::Bool)
--                   (_L::[a])
intT = mkType (Typ (HsTyCon (PNT (PN (UnQual "Int") (G (PlainModule "Prelude") "Int" (N (Just loc0)))) (Type (TypeInfo {defType = Just Primitive, constructors = [], fields = []})) (N (Just loc0)))))
boolT = mkType (Typ (HsTyCon (PNT (PN (UnQual "Bool") (G (PlainModule "Prelude") "Bool" (N (Just loc0)))) (Type (TypeInfo {defType = Just Data, constructors = [ConInfo {conName = PN "False" (G (PlainModule "Prelude") "False" (N (Just loc0))), conArity = 0, conFields = Nothing},ConInfo {conName = PN "True" (G (PlainModule "Prelude") "True" (N (Just loc0))), conArity = 0, conFields = Nothing}], fields = []})) (N (Just loc0)))))
listT = mkType (Typ (HsTyApp (Typ $ HsTyCon (PNT (PN (Qual (PlainModule "Prelude") "[]") (G (PlainModule "Prelude") "[]" (N (Just loc0)))) (Type (TypeInfo {defType = Just Data, constructors = [ConInfo {conName = PN "[]" (G (PlainModule "Prelude") "[]" (N (Just loc0))), conArity = 0, conFields = Nothing},ConInfo {conName = PN ":" (G (PlainModule "Prelude") ":" (N (Just loc0))), conArity = 2, conFields = Nothing}], fields = []})) (N (Just loc0)))) (Typ $ HsTyVar (PNT (PN (UnQual "a") (S loc0)) (Type (TypeInfo {defType = Nothing, constructors = [], fields = []})) (N (Just loc0))))))

mkType typ = Exp $ HsParen $ typedExp "_L" typ
typedExp strVar typ = Exp (HsExpTypeSig loc0 (nameToExp strVar) [] typ)

