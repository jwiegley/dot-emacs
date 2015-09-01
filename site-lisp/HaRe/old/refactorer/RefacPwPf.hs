-----------------------------------------------------------------------------
-- |
-- Module      :  RefacPwPf
-- Copyright   :  (c) Jose Proenca 2005
-- License     :  GPL
--
-- Maintainer  :  jproenca@di.uminho.pt
-- Stability   :  experimental
-- Portability :  portable
--
-- Refactoring tool that converts a pointwise to a pointfree expression.
--
-- It uses the modules "GlobalPW", "PWCore", "PwPfConversion" and "Pointfree"
--
-----------------------------------------------------------------------------

module RefacPwPf(
  -- * Refactoring  
  {-| Converts an expression in pointwise to pointfree by the following steps:

        (1) Reads the expression to be evaluated obtained by programatica's tools;

        (2) Tries to convert the expression to a 'GLTerm' by the use of the
            monadic function 'exp2Global', in "GlobalPW" module;
        
        (3) Converts the 'GLTerm' to a 'PWTerm', which is more general pointwise
            representation that can be found in module "PWCore", by the use of
            the function 'global2core';

        (4) Converts the 'PWTerm' to a 'PFTerm', which is a pointfree expression,
            by the use of the function 'core2Pf';

        (5) Writes the resulting pointfree expression into an expression of
            programatica's abstract syntax tree, by the use of the function 'pf2Exp'.
  -}
  pwToPf

 -- * Limitations
 {- | This refactoring is not complete, since only the grammar specified for
    the function 'exp2Global' can be recognized,
    and later translated into a pointfree expression.

    There are also some limitations. Some of them are presented bellow.

        * Types inside /IN/, /OUT/ and /PARA/ have the type information correct, but
          the variable \"_L\" sometimes don't have the correct location information,
          and lists are represented by @[a]@, where the letter @a@ may already be bounded; 

        * The source location information is ignored in most cases, since the
          expression is completely changed;

        * Scope information is lost, except for prelude functions;

        * Aditional information to the expression, like type information, cannot
          be added inside the selected expression, since only the specified grammar
          is recognized.
 -}

 ) where

import Prelude hiding (putStr)
import AbstractIO (putStr)
import RefacUtils

import GlobalPW (exp2Global, global2core)
import Pointfree (pf2Exp)
import PwPfConversion (core2Pf)


--pwToPf ::  [String] -> State' IO ()

pwToPf args  
  = do let fileName = args!!0              
           beginPos = (read (args!!1), read (args!!2))::(Int,Int)
           endPos   = (read (args!!3), read (args!!4))::(Int,Int)
       parseRes@(inscopes, exports, mod, toks) <- parseSourceFile fileName 
       let exp = locToExp beginPos endPos toks mod
       refactoredMod <- applyRefac (pwToPf exp) (Just parseRes) fileName
       writeRefactoredFiles False [refactoredMod]
    where 
     pwToPf exp (_,_,mod) = 
       do mod1 <- applyTP (once_tdTP (failTP `adhocTP` inExp)) $ mod
          mod2 <- addImports mod1 ["PointlessP.Combinators"
                                  ,"PointlessP.Functors"
                                  ,"PointlessP.Isomorphisms"
                                  ,"PointlessP.RecursionPatterns"
                                  ]
          return mod2
       where
        inExp exp1@(Exp _) 
           | sameOccurrence exp exp1 =
                    do global <- exp2Global exp1
                       let newExp = pf2Exp.core2Pf.global2core $ global
                       update exp newExp exp
                               
        inExp _ = mzero
        
        addImports = foldM myAddImport

        --myAddImport :: HsModule -> String -> m HsModule
        myAddImport mod strImp  
            | not $ strImp `isInMods` (hsModImports mod)
                   = addImportDecl mod strImp False Nothing False []
            | otherwise = return mod
          where 
                isInMods str  = or . map (isPlainWith str)

                str `isPlainWith` imp = 
                        case hsImpFrom imp of
                           SN (PlainModule str2) _ -> str == str2
                           _ -> False
