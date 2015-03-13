
module Main where

import Test.HUnit
import System.IO
import qualified System.Cmd as System
import System.Exit
import System.Environment
import Data.List

data TestCases = TestCases {refactorCmd::String
                           ,refactorCacheCmd::String
                           ,positive::[([String],[[String]],[String])]
                           ,negative::[([String],[[String]],[String])]}
  deriving (Show,Read)


createNewFileName str fileName 
  =let (name, posfix)=span (/='.') fileName
   in (name++str++posfix)

positiveTest system pfeCmd refactorCmd refactorCacheCmd args 
    =TestCase (do let inputFiles=(\(a,_,_)->a) args
                      tokExpOutputFiles=map (createNewFileName "_TokOut") inputFiles
                      --astExpOutputFiles=map (createNewFileName "_AstOut") inputFiles
                      --astActOutputFiles=map (createNewFileName "AST") inputFiles
                      tempFiles = map (createNewFileName "_temp") inputFiles
                      keepFiles = map (createNewFileName "_refac") inputFiles -- ++AZ++
                      params =refactorCmd: ((head inputFiles) : (third args))
                      caches = createCache refactorCacheCmd ((\(_,a,_)->a) args) (head inputFiles)
                      inputTemps =zip inputFiles tempFiles
                      inputOutputs1=zip inputFiles tokExpOutputFiles
                      --inputOutputs2=zip astActOutputFiles astExpOutputFiles
                  mapM (createTempFile system) inputTemps
                  performCaches system pfeCmd caches
                  system ("echo " ++ concatMap (\t->t ++ " ") params ++ " |" ++ pfeCmd)

                  mapM (keepResult system) $ zip inputFiles keepFiles -- ++AZ++
                  
                  results1<-mapM (compareResult system) inputOutputs1
                  --results2<-mapM (compareResult system) inputOutputs2
                  mapM (recoverFiles system) inputTemps
                  mapM (rmTempFiles system) tempFiles
                  -- mapM (rmTempFiles system) astActOutputFiles
                  assertEqual (show (refactorCmd,args)) True (all (==ExitSuccess) (results1)) -- ++results2)) 
              )

performCaches _ _ [] = return ()
performCaches system pfeCmd (x:xs) = 
 do
    system ("echo " ++ concatMap (\t -> t ++ " ") x ++ " |" ++ pfeCmd)
    performCaches system pfeCmd xs

createCache _ [] file = []
createCache refactorCacheCmd (a:as) file
   = (refactorCacheCmd : (file : a)) : (createCache refactorCacheCmd as file)

negativeTest system pfeCmd refactorCmd refactorCacheCmd args
    =TestCase (do let inputFiles = (\(a,_,_)->a) args
                      tokExpOutputFiles=map (createNewFileName "_TokOut") inputFiles
                      tempFiles = map (createNewFileName "_temp") inputFiles
                      params =refactorCmd: ((head inputFiles) : (third args))
                      caches = createCache refactorCacheCmd ((\(_,a,_)->a) args) (head inputFiles)
                      inputTemps =zip inputFiles tempFiles
                      inputOutputs=zip inputFiles tokExpOutputFiles
                  mapM (createTempFile system) inputTemps
                  performCaches system pfeCmd caches
                  system ("echo " ++ concatMap (\t->t ++ " ") params ++ " |" ++ pfeCmd) 
                  results<-mapM (compareResult system) inputOutputs
                  mapM (recoverFiles system) inputTemps
                  mapM (rmTempFiles system) tempFiles
                  assertEqual (show (refactorCmd,args)) True (all (==ExitSuccess) results) 
              )

third :: ([String],[[String]],[String]) -> [String]
third (x,y,z) = z
     
createTempFile system (input, temp)=system ("cp "++ input++ " "++temp)

keepResult system (input, keep)=system ("cp "++ input++ " "++keep)

-- compareResult system (input,output)=system ("diff "++input++ " " ++ output)
compareResult system (input,output)=system ("diff --strip-trailing-cr "++input++ " " ++ output) -- ++AZ++

recoverFiles system (input ,temp)= system ("cp " ++ temp ++ " " ++input)

rmTempFiles system temp = system ("rm "++temp)

testCases system pfeCmd refactorCmd refactorCacheCmd positiveTests negativeTests
     =TestList ((map (positiveTest system pfeCmd refactorCmd refactorCacheCmd) positiveTests)
             ++ (map (negativeTest system pfeCmd refactorCmd refactorCacheCmd) negativeTests))


runTesting system hare refactorCmd refactorerCacheCmd positiveTests negativeTests
     =do let files=concatMap (\t->t++" ") $ nub (concatMap (\(a,_,_) ->a) positiveTests) ++ (concatMap (\(a,_,_) ->a) negativeTests)
         system ("echo new |" ++ hare)
         system ("echo add " ++ files ++ " |" ++ hare)
         system ("echo chase ../../tools/base/tests/HaskellLibraries/ |" ++ hare)
         system ("echo chase . |" ++ hare)
         runTestTT (testCases system hare refactorCmd refactorerCacheCmd positiveTests negativeTests) 



main  = do
  [bash,hare] <- getArgs
  f <- readFile "UTest.data" 
  let testcases = read f::TestCases
  runTesting (system bash) hare 
             (refactorCmd testcases)
             (refactorCacheCmd testcases)
             (positive testcases)
             (negative testcases)


system bash cmd = --(hPutStrLn stderr cmd')>>
  (System.system cmd')
   where
      -- cmd' = cmd 
      cmd' = bash++" -c \""++cmd++" >> log.txt 2>>log.txt\""
