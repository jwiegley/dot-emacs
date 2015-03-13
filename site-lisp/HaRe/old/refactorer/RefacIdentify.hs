module RefacIdentify where

import System.IO.Unsafe
import PosSyntax hiding (ModuleName, HsName, SN)
import SourceNames
import ScopeModule
import UniqueNames hiding (srcLoc)
import HsName
import HsLexerPass1
import PNT
import TiPNT
import SimpleGraphs(reverseGraph,reachable)
import HsTokens
import PrettyPrint
import RefacTypeSyn
import RefacLocUtils
import Data.Char
import GHC.Unicode
import AbstractIO
import Data.Maybe
import Data.List
import Data.Function
import RefacUtils
import LocalSettings (answerFilePath,transFilePath,classAnswerPath, classTransformPath)

-- this module is used to identify the clone class we are interested in.
-- we use the highlighted expression passed in, and write the clone class
-- to a separate file for use with parseAnswers.

refacIdentify args
  = do
       AbstractIO.putStrLn "refacIdentify"
       let fileName = ghead "fileName'" args
           beginRow         = read (args!!1)::Int
           beginCol         = read (args!!2)::Int
           endRow           = read (args!!3)::Int
           endCol           = read (args!!4)::Int

       AbstractIO.writeFile answerFilePath ""
       -- collect the answers...
       (inscps, exps, mod, tokList)<-parseSourceFileOld fileName
       let subExp = locToExp (beginRow, beginCol) (endRow, endCol) tokList mod
       expression <- AbstractIO.readFile transFilePath
       let expressions = (read expression)::([ [(HsExpP, String, String)] ])
           clonedExps = concat (filter (subExp `myElem`) expressions)

       -- write the clone class to two files for analysis.
       AbstractIO.writeFile classAnswerPath $ show clonedExps
       AbstractIO.writeFile classTransformPath $ show clonedExps


       AbstractIO.putStrLn "Clone class identified."

myElem :: HsExpP -> [(HsExpP, String, String)] -> Bool
myElem _ [] = False
myElem e ((x,y,z):xs)
 -- | toRelativeLocs e == toRelativeLocs x    = True
 | findEntityWithLocation e x = True
 | otherwise = myElem e xs
