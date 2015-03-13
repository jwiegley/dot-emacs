-- $Id: Translate.hs,v 1.1 2001/03/19 17:55:45 moran Exp $

module Translate where

import Syntax
import List((\\))

type Translator a b = [Name] -> [Name] -> a -> b


translateProp :: Translator Prop EscProp
translateProp metas env (Eval p) =
    EscEval $ translateE translateProp metas env p
translateProp metas env (Prop p) =
    EscProp $ translateP (translateId Var) codeExp translateProp metas env p
	where codeExp metas env e = Code $ translateExp metas env e
translateProp metas env (Term e) =
    EscTerm $ Code $ translateExp metas env e

translateExp :: Translator Exp EscExp
translateExp metas env (ExpEval e) =
    EscExpEval $ translateE translateExp metas env e
translateExp metas env (ExpId v) =
    EscExpId $ translateId Escape metas env v


translateId :: (Name -> Id) -> Translator Id Id
translateId meta metas env (Var v) =
    if v `elem` metas then meta v else Var v
translateId meta metas env v       = v


translateE :: Translator ea eb -> Translator (E ea Name) (E eb Name)
translateE te metas env (App e f)     = App (te metas env e) (te metas env f)
translateE te metas env (Lambda vs e) = Lambda vs $
				        te (metas \\ vs) (env ++ vs) e


translateP :: Translator Id Id -> Translator ta tb -> Translator pa pb ->
	      Translator (P Id ta pa) (P Id tb pb)
translateP ti tt tp metas env (p1 `And` p2)     =
    (tp metas env p1) `And` (tp metas env p2)
translateP ti tt tp metas env (p1 `Or` p2)      =
    (tp metas env p1) `Or` (tp metas env p2)
translateP ti tt tp metas env (p1 `Implies` p2) =
    (tp metas env p1) `Implies` (tp metas env p2)
translateP ti tt tp metas env (p1 `Iff` p2)     =
    (tp metas env p1) `Iff` (tp metas env p2)
translateP ti tt tp metas env (t1 `Equiv` t2)   =
    (tt metas env t1) `Equiv` (tt metas env t2)
translateP ti tt tp metas env (Exists i p)      =
    Exists (ti metas env i) (tp (nameOf i : metas) env p)
translateP ti tt tp metas env (All i p)         =
    All (ti metas env i) (tp (nameOf i : metas) env p)
translateP ti tt tp metas env Truth             = Truth
translateP ti tt tp metas env Falsehood         = Falsehood


nameOf (Var n)    = n
nameOf (Escape n) = n