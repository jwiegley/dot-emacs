module LocalSettings where
import System.FilePath.Posix
import System.IO.Unsafe
import Paths_HaRe

root=getDataFileName "haskell-refac.el"

hare_version="HaRe 01/08/2012"

-- release_root      = showNoQuotes "/Users/chrisbrown/hare/cabal/HaRe_28062010/editors/.."
release_root = haskellLibraries


-- refactorer        = showNoQuotes "/Users/chrisbrown/hare/cabal/HaRe_28062010/refactorer/pfe"
refactorer        = showNoQuotes "pfe" -- We will assume that Cabal installs it on our path

-- refactorer_client = showNoQuotes "/Users/chrisbrown/hare/cabal/HaRe_28062010/refactorer/pfe_client"

preludePath       = unsafePerformIO $ getDataFileName "HaskellLibraries"

reportFilePath     = unsafePerformIO $ getDataFileName "dupReport"
answerFilePath     = unsafePerformIO $ getDataFileName "dupAnswers"
positionFilePath   = unsafePerformIO $ getDataFileName "dupPositions"
transFilePath      = unsafePerformIO $ getDataFileName "dupTransforms"
classAnswerPath    = unsafePerformIO $ getDataFileName "dupClassAnswer"
classTransformPath = unsafePerformIO $ getDataFileName "dupClassTransform"
mergeFilePath      = unsafePerformIO $ getDataFileName "mergeCache"
evalFilePath       = unsafePerformIO $ getDataFileName "evalCache.txt"

evaluate = "hare-evaluate"
evaluate_result = unsafePerformIO $ getDataFileName "evaluateResult"

genFoldPath = unsafePerformIO $ getDataFileName "genFoldCache"

(refactor_prg:refactor_args) = words refactorer -- for emacs
showNoQuotes x = init $ tail $ show x

haskellLibraries = dropFileName (unsafePerformIO $ getDataFileName "Prelude.hs")
