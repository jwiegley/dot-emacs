#!/usr/bin/runhaskell

import Distribution.Simple
import Distribution.Simple.Setup (ConfigFlags (..))
import Distribution.PackageDescription (emptyHookedBuildInfo,HookedBuildInfo(..))
import Language.Haskell.HsColour (hscolour,Output(CSS))
import Language.Haskell.HsColour.Colourise (defaultColourPrefs)
import Control.Monad
import Data.Maybe
import Data.List

main :: IO ()
main = defaultMainWithHooks hooks

hooks :: UserHooks
hooks = simpleUserHooks { preConf = myPreConf }

-- read template file with markers, call replaceOrEcho for each marker
myPreConf :: Args -> ConfigFlags -> IO HookedBuildInfo
myPreConf _ _ = do
  putStr "Generating custom html documentation... "
  -- file <- readFile "data/astview-tmpl.html"
  replaced <- mapM replaceOrEcho . lines =<< readFile "data/astview-tmpl.html"

  putStrLn " done."
  writeFile "data/astview.html" (unlines . concat $ replaced)
  return emptyHookedBuildInfo

-- echoes the current line, or, if mymatch succeeds:
-- replaces the line with colourized haskell code.
replaceOrEcho :: String -> IO [String]
replaceOrEcho s = 
  if not $ match s 
    then return [s]
    else do
      putStr $ (extract s)++" "
      file <- readFile ("data/"++(extract s)++".hs.txt")
      let replacement = lines $ hscolour 
                  CSS 
                  defaultColourPrefs 
                  False 
                  True 
                  (extract s) 
                  False 
                  file
      return (["<!-- Example "++(extract s)++" follows: -->"]
             ++ replacement
             ++ ["<!-- Example "++(extract s)++" done. -->"])


-- interface that delegates to various implementations:

-- recognizes Template marker of the form "%%asdf%%"
match :: String -> Bool
match = match0 "%%"

--extracts the filename from the marker
extract :: String -> String
extract = extract1 "%%"

--------  Implementations  --------------

match0 :: String -> String -> Bool
match0 p s = take 2 s == p && take 2 (reverse s) == p

match1 :: String -> String -> Bool
match1 p = liftM2 (&&) 
             (help p) 
             (help p . reverse) 
  where help q = (q ==) . (take (length q))

match2 :: String -> String -> Bool
match2 p s = p `isSuffixOf` s && (reverse p) `isPrefixOf` s

extract1 :: String -> String -> String
extract1 p s = let remainder = (drop (length p) s) in reverse (drop (length p) (reverse remainder) )

extract2 :: String -> String -> String
extract2 p s = reverse (drop (length p) (reverse (drop (length p) s)))


extract3 :: String -> String -> String
extract3 p s = reverse . drop (length p) $ reverse $ drop (length p) s


extract4 :: String -> String
extract4 = help . reverse . help
  where help :: String -> String
        help = fromJust . (stripPrefix "%%%")
