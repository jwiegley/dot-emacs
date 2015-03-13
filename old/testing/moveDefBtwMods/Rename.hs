module Rename where

import System

rename inputFile
 = do let inputFile'=inputFile++".hs"
          tokExpOutputFile=inputFile++"_TokOut.hs"
          astExpOutputFile=inputFile++"_AstOut.hs"
          astActOutputFile=inputFile++"AST.hs"
          tempFile=inputFile++"_temp.hs"
      system ("cp "++ inputFile' ++ " "++ tokExpOutputFile)
      system ("cp " ++ astActOutputFile ++ " "++astExpOutputFile)
      system ("cp " ++ tempFile ++ " "++inputFile')
      system ("rm " ++ astActOutputFile)
      system ("rm "  ++ tempFile)
{-
main = do cmdLine<-getArgs
          doRename (head cmdLine) -}
{-
temp  = do cmdLine <-getArgs
           doCreateTemp (head cmdLine) -}

temp inputFile 
  = system ("cp " ++ inputFile ++".hs "++ inputFile++"_temp.hs")

