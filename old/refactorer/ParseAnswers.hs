-----------------------------------------------------------------------------
-- |
-- Module      :  ParseAnswers
-- Copyright   :  (c) Christopher Brown 2007
--
-- Maintainer  :  cmb21@kent.ac.uk
-- Stability   :  provisional
-- Portability :  portable
-- This module parses a file containing a list of questions
-- asking the user to replace occurences of duplicated code with
-- a function call.
-- After reading the question the module removes the question from the
-- file until finally an empty file is passed in.
--
-- If an empty file is passed in the module does exactly nothing.
--
-----------------------------------------------------------------------------

module ParseAnswers where

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
import RefacTypeSyn
import RefacLocUtils
import GHC
import Data.Char
import GHC.Unicode
import AbstractIO
import Data.Maybe
import Data.List
import RefacUtils
import LocalSettings
import PrettyPrint
parseAnswers args
  = do
       if (length args) > 0
         then do
          let answers = args!!0
          -- AbstractIO.putStrLn answers
          AbstractIO.appendFile answerFilePath (answers ++ "\n")
          {- answer <- AbstractIO.readFile reportFilePath
          let (answer2, remainder) = parseAnswer (force answer)
          if remainder == "" && answer2 == ""
            then do
             AbstractIO.putStrLn $ "completed."
            else do
             AbstractIO.putStrLn answer2
             AbstractIO.writeFile reportFilePath remainder -}
         else do
          answer <- AbstractIO.readFile classAnswerPath
          let (answer2, remainder) = parseAnswer (force (read answer::[(HsExpP, String, String)]))
          if remainder == [] && answer2 == ""
            then do
             AbstractIO.putStrLn $ "completed."
            else do
             AbstractIO.putStrLn answer2
             AbstractIO.writeFile classAnswerPath $ show remainder

parseAnswer :: [ (HsExpP, String, String) ] -> (String, [ (HsExpP, String, String) ])
parseAnswer [] = ("", [])
parseAnswer ((x,y,z):xs)
 = ( z , xs)


force  :: Eq a => a -> a
force x = if x==x then x else x
{-
parseAnswer :: String -> (String, String)
parseAnswer [] = ([], [])
parseAnswer ('<':'%':'>':xs)
 = (parseEnd xs, parseAfter xs)
parseAnswer ('\n' : xs)
 = parseAnswer xs
parseAnswer (x:xs)
 = ((x: parseEnd xs), parseAfter xs)

parseEnd :: String -> String
parseEnd [] = []
parseEnd ('<':'&':'>': xs)
  = []
parseEnd (x:xs)
   = x : parseEnd xs

parseAfter :: String -> String
parseAfter [] = []
parseAfter ('<':'&':'>': xs)
 = xs
parseAfter (x:xs)
 = parseAfter xs -}
