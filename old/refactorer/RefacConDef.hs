module RefacConDef (subConstantDef) where

import PrettyPrint
import PosSyntax
import AbstractIO
import Data.Maybe
import TypedIds
import UniqueNames hiding (srcLoc)
import PNT
import TiPNT
import Data.List
import RefacUtils
import PFE0 (findFile)
import MUtils (( # ))

-- folding against a constant definition

subConstantDef args
  = do let fileName   = args!!0
           beginRow   = read (args!!1)::Int
           beginCol   = read (args!!2)::Int
           endRow     = read (args!!3)::Int
           endCol     = read (args!!4)::Int
       AbstractIO.putStrLn "subConstantDef"

       (inscps, exps, mod, tokList) <- parseSourceFile fileName


       let (pnt,subExp) = findDefNameAndExp tokList (beginRow, beginCol) (endRow, endCol) mod
       
       if isPatBind pnt 
         then do
           -- constant folding...
           
         else do
           -- function folding
       
           let exp = locToExp (beginRow, beginCol) (endRow, endCol) tokList mod
           (mod', ((tokList', m) , _)) <- runStateT (doSubstitution pnt exp mod) ((tokList,False),( 0, 0))
           writeRefactoredFiles False [((fileName, m), (tokList', mod'))]

findDefNameAndExp toks beginPos endPos t
   = fromMaybe (defaultPNT, defaultExp) (applyTU (once_tdTU (failTU `adhocTU` inMatch
                                                                    `adhocTU` inPat)) t)  --CAN NOT USE 'once_tdTU' here.

    where  --The selected sub-expression is in the rhs of a match
          inMatch (match@(HsMatch loc1  pnt pats rhs ds)::HsMatchP)
            | locToExp beginPos endPos toks rhs /= defaultExp
            = Just (pnt, locToExp beginPos endPos toks rhs)
          inMatch _ = Nothing

          --The selected sub-expression is in the rhs of a pattern-binding
          inPat (pat@(Dec (HsPatBind loc1 ps rhs ds))::HsDeclP)
            | locToExp beginPos endPos toks rhs /= defaultExp
            = if isSimplePatBind pat
               then Just (patToPNT ps, locToExp beginPos endPos toks rhs)
               else error "A complex pattern binding can not be generalised!"
          inPat _ = Nothing


doSubstitution p e = applyTP (stop_tdTP (failTP `adhocTP` subExp))
                       where
                             subExp exp@((Exp _)::HsExpP)
                               | sameOccurrence exp e == False = if toRelativeLocs e == toRelativeLocs exp then 
                                                                                   update exp (createFunc p) exp
                                                                             else
                                                                                   mzero
                               | otherwise                     = mzero

                             createFunc pat =
                                              (Exp (HsId (HsVar pat))) 

