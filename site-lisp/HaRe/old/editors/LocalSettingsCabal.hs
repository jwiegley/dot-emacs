module LocalSettingsCabal where

import Paths_HaRe
import GHC.Paths ( libdir )
--GHC.Paths is available via cabal install ghc-paths

-- rELEASE_ROOT =


hare_version = version


-- release_root= showNoQuotes "${RELEASE_ROOT}"
--release_root = getDataFileName "."
release_root = "."

{-
refactorer = showNoQuotes "${REFACTORER}"
refactorer_client = showNoQuotes "${REFACTORER_CLIENT}"
preludePath = "${PRELUDE}"
-}

reportFilePath = release_root ++ "/refactorer/duplicate/report.txt"

answerFilePath = release_root ++ "/refactorer/duplicate/answers.txt"
{-
positionFilePath = "${RELEASE_ROOT}/refactorer/duplicate/positions.txt"
-}
transFilePath  = release_root ++ "/refactorer/duplicate/transforms.txt"

classAnswerPath    = release_root ++ "/refactorer/duplicate/classAnswer.txt"

classTransformPath = release_root ++ "/refactorer/duplicate/classTransform.txt"

mergeFilePath  = release_root ++ "/refactorer/merging/mergeCache.txt"

ghcPath = libdir

evalFilePath = release_root ++ "/refactorer/evalMon/evalCache.txt"

-- ++AZ++: this is an executable, need, to see if it can become a straight function call
evaluate = release_root ++ "/refactorer/evaluate"
evaluate_result = release_root  ++ "/refactorer/evaluate_result"

genFoldPath = release_root ++ "/refactorer/genFoldCache.txt"
{-

(refactor_prg:refactor_args) = words refactorer -- for emacs
-}
showNoQuotes x = init $ tail $ show x
