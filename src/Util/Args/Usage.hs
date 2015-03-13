module Util.Args.Usage (usage) where

import Util.Args.ArgDescr (ArgDescr(..), DefaultValue(..))
import Data.Function (on)
import Util.WordWrap (wordWrap)
import Data.List(sortBy)
import Util.Args.ArgArrow (ArgArrow, getKnownArgs)
import Util.String (padTo)
import System.Environment (getProgName)

-- pretty prints cli arg description for usage
-- left column contains cli arg header (e.g. '--verbose', or '--binary=PATH')
-- right column contains info messages for that argument
-- returns list of lines
showFlagDescr :: ArgDescr -> [String]
showFlagDescr argDescr = zipWith makeLine lefts helpLines
    where lefts    = argLine : repeat ""
          argLine  = case argDescr of
                       SwitchDescr name _ Nothing -> "--" ++ name
                       SwitchDescr name _ (Just c) ->
                           concat ["-", [c], " ", "--", name]
                       ValArg name tmpl _ _ -> concat ["--", name, "=", tmpl]
          msgLines = wordWrap 60 $ case argDescr of
                                     SwitchDescr _ hlp _ -> hlp
                                     ValArg _ _ default' help ->
                                         concat [help, "\n", defaultsLine default']
          helpLines = if length argLine < 18 then
                          msgLines
                      else
                          "" : msgLines -- line with argument is too long
                                        -- make more room for it
          defaultsLine (ConstValue s) = concat ["(defaults to '", s, "')"]
          defaultsLine (DynValue s)   = concat ["(defaults to ", s, ")"]
          makeLine infoLine descrLine = (infoLine `padTo` 20) ++ descrLine

-- returns string with formatted cli arg usage help message
-- argument descriptions are extracted from arg parsing computation
-- adds simple header and appends provided footer
usage :: ArgArrow a b -> String -> IO String
usage arrow outro = do
  self <- getProgName
  let intro = "usage: " ++ self ++ " [FLAGS]"
  return $ unlines $ [intro, "", "Flags:"] ++ flagsDescr ++ [""] ++ [outro]
      where flagsDescr = concatMap showFlagDescr $ argDescrSort $ getKnownArgs arrow
            argDescrSort = sortBy (compare `on` argName)
