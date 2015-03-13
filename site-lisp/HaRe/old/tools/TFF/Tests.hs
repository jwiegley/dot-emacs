module Main where


import TypesTerms
import Preds
import Syntax
import PrettyPrint
import TFFMonad

import System(getArgs)


--------------------------------------------------------------------------------
-- Tests
--

free f@(Exp (HsId (HsVar n)) , t) = do
    { putStrLn $ "Theorem for: " ++ pp f
    ; putStrLn . pp . run $ getRel t f f
    }



a = mkTyVar (UnQual "a")
b = mkTyVar (UnQual "b")
c = mkTyVar (UnQual "c")

tint = mkTyCon (UnQual "Int")
tchar = mkTyCon (UnQual "Char")

(+->) = mkTyFun

fall n t = mkTyAll (UnQual n) t

mkVar = hsEVar . UnQual

t0 = free (mkVar "one", tint)
t1_0 = free (mkVar "succ", (tint +-> tint))
t1 = free (mkVar "succN", (tint +-> tchar +-> tchar))
t2 = free (mkVar "bottom", (fall "a" a))
t3 = free (mkVar "const1", (fall "a" (a +-> tint)))
t4 = free (mkVar "cast",   (fall "a" (fall "b" (a +-> b))))
t5 = free (mkVar "const",   (fall "a" (fall "b" (a +-> (b +-> a)))))

tsts = [t0, t1_0, t1, t2, t3, t4, t5]


main = do
    a:args <- getArgs
    let x = (read a) :: Int
    tsts !! x
    return ()



--
--------------------------------------------------------------------------------


