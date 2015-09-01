module Language.Haskell.Refact.Refactoring.Case(ifToCase) where

import qualified Data.Generics         as SYB
import qualified GHC.SYB.Utils         as SYB

import qualified GHC           as GHC

import Control.Monad
import Control.Monad.IO.Class
import Language.Haskell.GhcMod
import Language.Haskell.Refact.API

-- ---------------------------------------------------------------------

-- | Convert an if expression to a case expression
ifToCase :: RefactSettings -> Cradle -> FilePath -> SimpPos -> SimpPos -> IO [FilePath]
ifToCase settings cradle fileName beginPos endPos =
  runRefacSession settings cradle (comp fileName beginPos endPos)

comp :: FilePath -> SimpPos -> SimpPos -> RefactGhc [ApplyRefacResult]
comp fileName beginPos endPos = do
       getModuleGhc fileName
       renamed <- getRefactRenamed
       logm $ "Case.comp:renamed=" ++ (SYB.showData SYB.Renamer 0 renamed) -- ++AZ++
       let expr = locToExp beginPos endPos renamed
       -- logm $ "Case.comp:expr=" ++ (SYB.showData SYB.Renamer 0 expr) -- ++AZ++
       case expr of
         Just exp1@(GHC.L _ (GHC.HsIf _ _ _ _))
                -> do (refactoredMod,_) <- applyRefac (doIfToCaseInternal exp1) RSAlreadyLoaded
                      return [refactoredMod]
         _      -> error $ "You haven't selected an if-then-else  expression!" --  ++ (show (beginPos,endPos,fileName)) ++ "]:" ++ (SYB.showData SYB.Parser 0 $ ast)

doIfToCaseInternal ::
  GHC.Located (GHC.HsExpr GHC.Name)
  -> RefactGhc ()
doIfToCaseInternal expr = do
  rs <- getRefactRenamed
  reallyDoIfToCase expr rs

reallyDoIfToCase ::
  GHC.Located (GHC.HsExpr GHC.Name)
  -> GHC.RenamedSource
  -> RefactGhc ()
reallyDoIfToCase expr rs = do

   void $ everywhereMStaged SYB.Renamer (SYB.mkM inExp) rs
   showLinesDebug "after refactoring"
   return ()
       where
         inExp :: (GHC.Located (GHC.HsExpr GHC.Name)) -> RefactGhc (GHC.Located (GHC.HsExpr GHC.Name))
         inExp exp1@(GHC.L l (GHC.HsIf _se (GHC.L l1 _) (GHC.L l2 _) (GHC.L l3 _)))
           | sameOccurrence expr exp1
           = do
               -- drawTokenTreeDetailed "reallyDoIfToCase" -- ++AZ++ debug
               newExp <- ifToCaseTransform exp1

               -- let (GHC.RealSrcLoc rl) = GHC.srcSpanStart l
               let caseTok = tokenise (gs2ss l) 0 False "case"
               condToks <- getToksForSpan l1
               let ofTok = tokenise
                     (gs2ss $ tokenSrcSpan (glast "reallyDoIfToCase" condToks))
                     -- (realSrcLocFromTok (glast "reallyDoIfToCase" condToks))
                           1 True "of"
               let trueToks = basicTokenise "True  ->"
               let falseToks = basicTokenise "False ->"
               thenToksRaw <- getToksForSpan l2
               elseToksRaw <- getToksForSpan l3

               let thenToks = dropWhile isEmpty thenToksRaw
               let elseToks = dropWhile isEmpty elseToksRaw

               logm $ "reallyDoIfToCase:elseToks=" ++ (show elseToks)

               let t0 = reIndentToks PlaceAdjacent caseTok condToks
               let t1' = reIndentToks PlaceAdjacent (caseTok ++ t0) ofTok
               let t1 = caseTok ++ t0 ++ t1'

               let t2 = reIndentToks (PlaceIndent 1 4 0) t1 trueToks
               let t3 = reIndentToks PlaceAdjacent (t1++t2) thenToks

               let (_,col) = tokenPos $ ghead "reallyDoIfToCase" t2

               let t4 = reIndentToks (PlaceAbsCol 1 col 0) (t1++t2++t3) falseToks
               -- logm $ "reallyDoIfToCase:(t1++t2++t3++t4)=" ++ (show (t1++t2++t3++t4))
               let t5 = reIndentToks PlaceAdjacent (t1++t2++t3++t4) elseToks

               let caseToks = t1++t2++t3++t4++t5 ++ [newLnToken (last t5)]

               logm $ "reallyDoIfToCase:t1=[" ++ (GHC.showRichTokenStream t1) ++ "]"
               logm $ "reallyDoIfToCase:t2=[" ++ (GHC.showRichTokenStream t2) ++ "]"
               logm $ "reallyDoIfToCase:t3=[" ++ (GHC.showRichTokenStream t3) ++ "]"

               -- logm $ "reallyDoIfToCase:t1++t2++t3=" ++ (show (t1++t2++t3))

               logm $ "reallyDoIfToCase:t4=[" ++ (GHC.showRichTokenStream t4) ++ "]"
               logm $ "reallyDoIfToCase:t5=[" ++ (GHC.showRichTokenStream t5) ++ "]"

               logm $ "reallyDoIfToCase:caseToks=" ++ (show caseToks)

               -- drawTokenTreeDetailed "reallyDoIfToCase"

               void $ putToksForSpan l caseToks

               -- drawTokenTree "reallyDoIfToCase after putToks"
               -- drawTokenTreeDetailed "reallyDoIfToCase after putToks"

               return newExp

         inExp e = return e

-- TODO: rearrange the structure and preserve the comments in the original, e.g. in e1,e2,e3
ifToCaseTransform :: GHC.Located (GHC.HsExpr GHC.Name) -> RefactGhc (GHC.Located (GHC.HsExpr GHC.Name))
ifToCaseTransform (GHC.L l (GHC.HsIf _se e1 e2 e3)) = do
  trueName  <- mkNewGhcName Nothing "True"
  falseName <- mkNewGhcName Nothing "False"
  let ret = GHC.L l (GHC.HsCase e1
             (GHC.MatchGroup
              [
                (GHC.noLoc $ GHC.Match
                 [
                   GHC.noLoc $ GHC.ConPatIn (GHC.noLoc trueName) (GHC.PrefixCon [])
                 ]
                 Nothing
                 ((GHC.GRHSs
                   [
                     GHC.noLoc $ GHC.GRHS [] e2
                   ] GHC.EmptyLocalBinds))
                )
              , (GHC.noLoc $ GHC.Match
                 [
                   GHC.noLoc $ GHC.ConPatIn (GHC.noLoc falseName) (GHC.PrefixCon [])
                 ]
                 Nothing
                 ((GHC.GRHSs
                   [
                     GHC.noLoc $ GHC.GRHS [] e3
                   ] GHC.EmptyLocalBinds))
                )
              ] undefined))
  return ret
ifToCaseTransform x = return x

-- ---------------------------------------------------------------------
{-
HsIf (Maybe (SyntaxExpr id)) (LHsExpr id) (LHsExpr id) (LHsExpr id)

[Can ignore The SyntaxExpr]


HsCase (LHsExpr id) (MatchGroup id)

-}

{-
Need to move to

(L {test/testdata/Case/B.hs:(9,10)-(11,17)} 
                 (HsCase 
                  (L {test/testdata/Case/B.hs:9:15-21} 
                   (HsPar 
                    (L {test/testdata/Case/B.hs:9:16-20} 
                     (HsApp 
                      (L {test/testdata/Case/B.hs:9:16-18} 
                       (HsVar {Name: GHC.Real.odd})) 
                      (L {test/testdata/Case/B.hs:9:20} 
                       (HsVar {Name: x})))))) 
                  (MatchGroup 
                   [
                    (L {test/testdata/Case/B.hs:10:3-15} 
                     (Match 
                      [
                       (L {test/testdata/Case/B.hs:10:3-6} 
                        (ConPatIn 
                         (L {test/testdata/Case/B.hs:10:3-6} {Name: GHC.Types.True}) 
                         (PrefixCon 
                          [])))] 
                      (Nothing) 
                      (GRHSs 
                       [
                        (L {test/testdata/Case/B.hs:10:11-15} 
                         (GRHS 
                          [] 
                          (L {test/testdata/Case/B.hs:10:11-15} 
                           (HsLit 
                            (HsString {FastString: "Odd"})))))] 
                       (EmptyLocalBinds)))),
                    (L {test/testdata/Case/B.hs:11:3-17} 
                     (Match 
                      [
                       (L {test/testdata/Case/B.hs:11:3-7} 
                        (ConPatIn 
                         (L {test/testdata/Case/B.hs:11:3-7} {Name: GHC.Types.False}) 
                         (PrefixCon 
                          [])))] 
                      (Nothing) 
                      (GRHSs 
                       [
                        (L {test/testdata/Case/B.hs:11:12-17} 
                         (GRHS 
                          [] 
                          (L {test/testdata/Case/B.hs:11:12-17} 
                           (HsLit 
                            (HsString {FastString: "Even"})))))] 
                       (EmptyLocalBinds))))] {!type placeholder here?!})))

from ---

(L {test/testdata/Case/B.hs:4:9-41} 
                 (HsIf 
                  (Nothing) 
                  (L {test/testdata/Case/B.hs:4:12-18} 
                   (HsPar 
                    (L {test/testdata/Case/B.hs:4:13-17} 
                     (HsApp 
                      (L {test/testdata/Case/B.hs:4:13-15} 
                       (HsVar {Name: GHC.Real.odd})) 
                      (L {test/testdata/Case/B.hs:4:17} 
                       (HsVar {Name: x})))))) 
                  (L {test/testdata/Case/B.hs:4:25-29} 
                   (HsLit 
                    (HsString {FastString: "Odd"}))) 
                  (L {test/testdata/Case/B.hs:4:36-41} 
                   (HsLit 
                    (HsString {FastString: "Even"})))))

-}

-- EOF



