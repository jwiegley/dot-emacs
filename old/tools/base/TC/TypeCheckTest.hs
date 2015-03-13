-- $Id: TypeCheckTest.hs,v 1.10 2001/04/19 17:36:08 pasalic Exp $

module TypeCheckTest where

import TypeCheck
import TypeGenerics
import Syntax
import HsName
import HsLiteral
import InferenceMonad

tst e = do { f <- newGensym ; 
             t <- newVar starKind ;
             (tr,cs) <- infer f [] env0 t e ; 
              return (visType tr, show cs)
       }

e1 = hsLambda [hsPVar (UnQual "x")] 
     (hsLambda [hsPVar (UnQual "y")] 
      (hsApp (hsEVar (UnQual "y")) (hsEVar (UnQual "x"))))

e2 = hsLambda [hsPVar (UnQual "x")] $
     hsApp (hsEVar (UnQual "x")) (hsLit (HsInt 4))

e3 = hsTuple [hsLit (HsInt 1), hsLit (HsInt 2)]

typeCheckDecls ds = runIM
    (do { f <- newGensym ;
          r <- inferDs f [] env0 ds ;
          return $ show r
    }) 0
                    
             
--visSch (Sch ks ps t) = (map visKind ks,map (map visType) ps, visType t)
--visPred (IsIn x ts) = (x,map visType ts)
             
typeCheckDs ds = runIM
    (do { f <- newGensym ;
          (ngv, env, ps) <- inferDs f [] env0 ds ;
          return (show env, show ps)
        }) 0

showEnv (x,a) = (show x)++" :: "++(show a)++"\n"


colEnv (x,a) = do { a' <- collapse a; return(x,a') }

performTC ds = 
  perform  (do { f <- newGensym 
               ; (ngv, env, ps) <- inferDs f [] (env0 {termEnv = simpleEnv}) ds
               ; env' <- mapM colEnv (take (length (getTermEnv env) - length simpleEnv) (getTermEnv env))
               ; return (concat (map showEnv env') ++ show ps)
               })