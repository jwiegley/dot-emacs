{-+ PFE command line parsing utilities
-}
module PfeParse(module PfeParse,arg,(<@),( #@ ),many) where
import Data.Char(isUpper)
import Control.Monad(when)
import Data.Maybe(isJust)

import HsName(ModuleName(..),sameModuleName,parseModuleName,isMainModule)
import TypedIds(NameSpace(..))

import PFE0(getCurrentModuleGraph,projectStatus)

import PrettyPrint(pp,(<+>),fsep)
import CmdLineParser3 as P
import MUtils((@@),( # ),concatMapM,swap,apBoth)

runCmds run cmds = run $ doCmd (cmds, projectStatus)

--type Cmd r = (String,(P r,String))

--doCmd :: ([Cmd (m ()], (m ())) -> String -> m ()
doCmd cmds _ = parseAll (cmdGrammar cmds)

cmdGrammar (cmds,default_cmd) =
    named "command" $
    foldr (!) (nil default_cmd)
          [nil id `chk` kw cmd <@ p :-- usage|(cmd,(p,usage))<-cmds]

usage prg cmds = P.usage prg (cmdGrammar (cmds,projectStatus))

kwOption w = isJust # opt (kw w)

noArgs = nil
args s f = f # many (arg s) -- s should now be in singular form!

filename = arg "<filename>"
filenames = many filename

fileArgs f = f # filenames
fileArg f = fileArgs (mapM_ f)

moduleArg f = moduleArgs (mapM_ f)
moduleArgs f = f @@ checkModuleNames # many (arg "<module>")

moduleArg' opts f = moduleArgs' opts (mapM_ . f)
moduleArgs' opts f = f' #@ opts <@ many (arg "<module>")
  where f' o = f o @@ checkModuleNames

checkModuleNames = concatMapM checkModuleName
checkModuleName s =
  do ms <- filter sameModule . map (fst.snd) # getCurrentModuleGraph
     when (null ms) $ fail (s++": unknown module")
     return ms
  where
    m = parseModuleName s
    sameModule = if isMainModule m then (==) m else sameModuleName s
    -- "Main{-file.hs-}" selects one particular Main module,
    -- "Main" select all main modules in a project

just ms = if null ms then Nothing else Just ms

idArgs f = f # many (arg "<identifier>")

qualIds f = (f @@ parseQualIds) # many (arg "<M.x>")
qualId f =  (f @@ parseQualId) # arg "<M.x>"

parseQualIds = mapM parseQualId
{-
parseOneQualId = parseQualId @@ one
  where
     one [q] = return q
     one qs = fail $ "Exactly one qualified name is required: "++unwords qs
-}

parseQualId s =
    case splitQualName s of
      Just (m,n) -> flip (,) n # checkModuleName1 m
             -- TODO: also check that m.n is defined!
      _ -> fail $ "Qaulified name required: "++s
  where
    splitQualName = fmap (apBoth reverse . swap) . split . reverse

    split s = case break (=='.') s of
		     (s1,'.':s2) -> Just (s1,s2)
		     _ -> Nothing
{-
    isQual s =
      case break (=='.') s of
	(c:_,'.':_:_) -> isUpper c
	_ -> False
-}
    checkModuleName1 = one @@ checkModuleName
      where
     one [q] = return q
     one qs = fail $ pp $ "Ambiguous module name:"<+>fsep qs

entityId f = (f' # opt idty) <@ arg "<M.x>"
  where
    f' ns = f . (,) ns @@ parseQualId

    -- This could be done with cmd and !,
    -- but the usage printer isn't good enough yet.
    idty = Token conv "type|class|value|con"

    conv arg | isClassOrType arg = Just ClassOrTypeNames
             | isValue       arg = Just ValueNames
             | otherwise         = Nothing

    isClassOrType arg = arg `elem` ["type","class"]
    isValue arg = arg `elem` ["value","con"]

{-
entityId f = Args "[type|class|value] <M.x>" (f @@ parseEntId)
  where
    parseEntId args0 = (,) ns # parseOneQualId args1
       where
         (ns,args1) =
           case args0 of
	     arg:args | isClassOrType arg -> (Just ClassOrTypeNames,args)
		      | isValue arg       -> (Just ValueNames,args)
	     _ -> (Nothing,args0)
         isClassOrType arg = arg `elem` ["type","class"]
	 isValue arg = arg `elem` ["value","con"]
-}
