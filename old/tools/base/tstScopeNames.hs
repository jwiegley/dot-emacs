import ParseHaskellProgram(parseHaskellProgram)
import ScopeHaskellProgram(scopeHaskellProgram)
import ScopeProgram
import PrettyPrint
import UTF8Util
import MUtils
import ParsedSyntax
import UniqueNames
import TypedIds

import List(sort)
import System(getArgs)
import Directory(doesDirectoryExist,createDirectory)

main = (test=<<getArgs) `catch` utf8err

test args =
  case args of
    "test":files -> tstScope files
    "xrefs":files -> crossRefs files
    _ -> fail "Usage: tstScopeNames (test|xrefs) <files>"

tstScope = putStrLn.upp.fst @@ scopeHaskellProgram @@ parseHaskellProgram
  where upp x = utf8 . pp $ x


crossRefs files = writeIt.scopeProgram' =<< parseHaskellProgram files
  where
    writeIt (mrs,mss) =
      do optCreateDirectory "hi"
         mapM_ writeRefs (simpmods mrs)
	 writeFile "hi/ModuleSourceFiles.txt" (show (map modfile (concat mss)))

    writeRefs (m,rs) = writeFile ("hi/"++m++".refs") (showl (sort rs))

    optCreateDirectory d = unlessM (doesDirectoryExist d) (createDirectory d)

    simpmods ms = [(m,simprefs refs)|(Module m,refs)<-ms]
    simprefs rs = [(simpp p,(show n,simpsp sp,map (simpos.getHSName) os))|
                    (sp,i,os)<-rs,
		    let PN n p=getHSName i]

    modfile m = (srcFile m,pp (hsModName m))
    
    simpsp ValueNames = V
    simpsp ClassOrTypeNames = T

    simpp (S s) = simpls s

    simpls (SrcLoc f r c) = (r,c)
    simpes (SrcLoc f r c) = (f,(r,c))

    simpos (PN n o) = simpo o
      where
        simpo (G (Module m) n) = Left (m,n)
        simpo (S s) = Right (simpes s)

data SP = V | T deriving (Show,Eq,Ord)

showl x = unlines . map show $ x
