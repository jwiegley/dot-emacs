
-- module GenEditorInterfaces where

-- library side for command line processing, command description,
-- and editor interface generation for Vim/GVim (Emacs to follow)

import System.Environment
import System.Exit
import Data.Maybe

import LocalSettings
import GenEditorInterfacesAux
import qualified Vim.EditorFunctions   as Vim
import qualified Emacs.EditorFunctions as Emacs

instance EditPars Comment (IO ())
  where
    editPars editFuns scriptPars p@(Comment comment) =
      let it c [] = c
          it c as = errorExit $ "no further parameters expected: "
                             ++ show as
          scr = (scriptFun editFuns scriptPars p)
      in Cmd{cmd         = it
            ,description = " "++comment
            ,script      = scr
            }

instance EditPars ps fps
      => EditPars (OptionPar ps) (String->fps)
  where
    editPars editFuns scriptPars p@(OptionPar isList option ps) =
      let ef = optionParFun editFuns scriptPars p
          c = editPars editFuns ef ps
          it f (a:as) = cmd c (f a) as
          it f []     = errorExit $ "Expected: "++desc
          desc = " <option ("++option++")>"++description c
      in Cmd{cmd         = it
            ,description = desc
            ,script      = script c
            }

instance EditPars ps fps
      => EditPars (NamePar ps) (String->fps)
  where
    editPars editFuns scriptPars p@(NamePar prompt ps) =
      let ef = nameParFun editFuns scriptPars p
          c = editPars editFuns ef ps
          it f (a:as) = cmd c (f a) as
          it f []     = errorExit $ "Expected: "++desc
          desc = " <name ("++prompt++")>"++description c
      in Cmd{cmd         = it
            ,description = desc
            ,script      = script c
            }

instance EditPars ps fps
      => EditPars (PathPar ps) (String->fps)
  where
    editPars editFuns scriptPars p@(PathPar prompt def ps) =
      let ef = pathParFun editFuns scriptPars p
          c = editPars editFuns ef ps
          it f (a:as) = cmd c (f a) as
          it f []     = errorExit $ "Expected: "++desc
          desc = " <pathname ("++prompt++"["++def++"])>"++description c
      in Cmd{cmd         = it
            ,description = desc
            ,script      = script c
            }

instance EditPars ps fps
      => EditPars (FileNamePar ps) (String->fps)
  where
    editPars editFuns scriptPars p@(FileNamePar keepExt ps) =
      let ef = fileNameParFun editFuns scriptPars p
          c = editPars editFuns ef ps
          it f (a:as) = cmd c (f a) as
          it f []     = errorExit $ "Expected: "++desc
          modifier = if keepExt then "" else "Base"
          desc     = " <file"++modifier++"Name>"++description c
      in Cmd{cmd         = it
            ,description = desc
            ,script      = script c
            }

instance EditPars ps fps
      => EditPars (PositionPar ps) (Int->Int->fps)
  where
    editPars editFuns scriptPars p@(PositionPar ps) =
      let ef = positionParFun editFuns scriptPars p
          c = editPars editFuns ef ps
          -- need to catch read errors here, for better message
          it f (ls:(cs:as)) = cmd c (f (read ls) (read cs)) as
          it f as           = errorExit $ "Expected: "++desc
                                       ++ "\nFound: "++show as
          desc = " <line> <column>"++description c
      in Cmd{cmd         = it
            ,description = desc
            ,script      = script c
            }

instance EditPars ps fps
      => EditPars (RegionPar ps) (Int->Int->Int->Int->fps)
  where
    editPars editFuns scriptPars p@(RegionPar ps) =
      let ef = regionParFun editFuns scriptPars p
          c = editPars editFuns ef ps
          -- need to catch read errors here, for better message
          it f (ls:(cs:(le:(ce:as)))) =
            cmd c (f (read ls) (read cs) (read le) (read ce)) as
          it f as = errorExit $ "Expected: "++desc
                             ++ "\nFound: "++show as
          desc  = " <line> <column> <line> <column>"++description c
      in Cmd{cmd         = it
            ,description = desc
            ,script      = script c
            }

help = do
  mapM_ (putStrLn . \(Entry entry name c)->entry++"("++name++")"++description c)
        (cmds defaultEditor)
  putStrLn "--"
  putStrLn "help               : display this usage information"
  putStrLn "pfeRefactoringCmds : generate module PfeRefactoringCmds"
  putStrLn "vim                : generate Vim binding"
  putStrLn "emacs              : generate Emacs binding"
  putStrLn ""


pfeRefactoringCmds = do
  let cmdlist = concatMap genEntry (cmds defaultEditor)
  putStrLn $ unlines
    ["-- refactoring commands added to pfe command interpreter"
    ,"-- this file is generated from GenEditorInterfaces.hs"
    ,"-- by calling the executable as follows:"
    ,"--   editors/GenEditorInterfaces pfeRefactoringCmds > refactorer/PfeRefactoringCmds.hs"
    ,""
    ,"module PfeRefactoringCmds where"
    ,""
    ,"import PfeParse"
    ,"import RefacMoveDef"
    ,"import RefacRenaming"
    ,"import RefacDupDef"
    ,"import RefacCacheMerge"
    ,"import RefacNewDef"
    ,"import RefacSlicTuple"
    ,"import RefacMerge"
    ,"import RefacRmDef"
    ,"import RefacAddRmParam"
    ,"import RefacGenDef"
    ,"import RefacMvDefBtwMod"
    -- ,"import InitGHC"
    ,"import DuplicateCode"
    ,"import RefacCleanImps"
    ,"import ParseAnswers"
    ,"import RefacAddCon"
    ,"import RefacTypeSig"
    ,"import RefacADT"
    ,"import RefacSwapArgs"
    ,"import RefacRedunDec"
    ,"import RefacSlicing"
    ,"import RefacDeForest"
    ,"import RefacUnGuard"
    ,"import RefacFunDef"
    -- ,"import RefacConDef"
    ,"import RefacAsPatterns"
    ,"import RefacUnfoldAsPatterns"
    ,"import RefacInstantiate"
    ,"import RefacDupTrans"
    ,"import RefacRemoveField"
    ,"import RefacAddField"
    ,"import RefacLetWhere"
    ,"import RefacRmCon"
    ,"import RefacWhereLet"
    ,"import RefacIntroPattern"
    ,"import RefacSimplify"
    ,"import RefacGenFold"
    ,"import RefacGenCache"
    ,"import RefacIdentify"
    -- TFP PAPER 2011
    ,"import RefacEvalMon"
    ,"import RefacAddEvalMonCache"
    ,"import RefacIntroThreshold"
    ,""
    ]
  putStrLn "pfeRefactoringCmds ="
  putStrLn "  ["
  printAddingCommas False cmdlist
  putStrLn "  ]"
  where
    printAddingCommas flag (entry@('-':('-':_)):rest) = do
      putStrLn $ "   "++entry
      printAddingCommas flag rest
    printAddingCommas flag (entry:rest) = do
      putStrLn $ (if flag then "  ," else "   ")++entry
      printAddingCommas True rest
    printAddingCommas flag [] =
      return ()
    genEntry (Entry entry cname cmd) =
      let (rComment,rPars)     = break (=='>') $ reverse $ description cmd
          (parameters,comment) = (reverse rPars,reverse rComment)
      in ["("++show cname++",(args "++show parameters++" "++cname++", "++show comment++"))"|entry/="undo"]
    genEntry (Menu entry cmds) | entry=="Projects" = []
    genEntry (Menu entry cmds) =
      (("-- menu "++entry):) $
      concatMap genEntry cmds

cmds editFuns = [Menu "Projects"
         [editParameters editFuns "New project" "new"
            new $ fileNamePar $
            comment "Start new project with current file"

         ,editParameters editFuns "Add file" "add"
            add $ fileNamePar $
            comment "Add current file to project"
         ,editParameters editFuns "Chase imports" "chase"
            chase $ optionPar True "chasePaths" $
            comment "Chase to add missing files to project"
         ,editParameters editFuns "List files" "files"
            files $
            comment "List files in project"

        ]

       ,Menu "Names/Scopes"
         [editParameters editFuns "Rename" "rename"
            rename $ fileNamePar $ namePar "New name? " $ positionPar $
            comment "Rename a variable name"

         ,editParameters editFuns "Lift def to top level" "liftToTopLevel"
            liftToTopLevel $ fileNamePar $ positionPar $
            comment "Lift a local declaration to top level"
         ,editParameters editFuns "Lift def one level" "liftOneLevel"
            liftOneLevel $ fileNamePar $ positionPar $
            comment "Lift a local declaration one level up"
         ,editParameters editFuns "Demote def" "demote"
            demote $ fileNamePar $ positionPar $
            comment "Demote a declaration to where it is used"
         ,editParameters editFuns "Create Type Signatures" "refacTypeSig"
            refacTypeSig $ fileNamePar $
            comment "Generates type signatures for top-level definitions using GHC."

         ,editParameters editFuns "ReadFile" "parseAnswers"
            parseAnswers $ fileNamePar $
            comment "Read in an answer"


         ,editParameters editFuns "Convert Let to Where" "letToWhere"
            letToWhere $ fileNamePar $ positionPar $
            comment "Converts a let expression into a where equation."

         ,editParameters editFuns "Convert Where to Let" "whereToLet"
            letToWhere $ fileNamePar $ positionPar $
            comment "Converts a where equation into a let expression"

         ,editParameters editFuns "Introduce patterns over an argument position" "introPattern"
            introPattern $ fileNamePar $ positionPar $
            comment "Replace variable with exhaustive set of patterns"

         ,editParameters editFuns "Introduce case analysis" "introCase"
            introCase $ fileNamePar $ positionPar $
            comment "Introduction of cases analysis via a pattern variable"

         ,editParameters editFuns "Fold term against pattern variable" "foldPattern"
            foldPattern $ fileNamePar $  namePar "Name of pattern variable: " $ regionPar $
            comment "Folds a sub-expression against a pattern variable"

         ]
       ,Menu "Slicing"
         [editParameters editFuns "Remove redundant declarations" "refacRedunDec"
          refacRedunDec $ fileNamePar $ regionPar $
          comment "Removes redundant declarations in a where clause or expression"

         ,editParameters editFuns "Slicing based on a subexpression" "refacSlicing"
           refacSlicing $ fileNamePar $ regionPar $
           comment "Slices a subexpression"
         ,editParameters editFuns "Slicing a tuple" "refacSlicTuple"
           refacSlicTuple $ fileNamePar $ positionPar $ namePar "Elements to slice: (A for all; (x,_x,_) for some): " $
           comment "slices a definition which returns a tuple"
         ,editParameters editFuns "Merge definitions" "refacMerge"
           refacMerge $ fileNamePar $ namePar "Name for new definition: " $
           comment "Merges multiple definitions to form one single definition."

         ,editParameters editFuns "Add definition for merge" "refacCacheMerge"
           refacCacheMerge $ fileNamePar $ positionPar $
           comment "Adds a definition to the cache for merging."
         ,editParameters editFuns "Instantiate a general pattern" "refacInstantiate"
           refacInstantiate $ fileNamePar $ positionPar $ namePar "patterns: " $
           comment "Instantiates patterns in a generalised function clause" ]

       ,Menu "Fold/Unfold"
         [editParameters editFuns "Unfold def" "unfoldDef"
            unfoldDef $ fileNamePar $ positionPar $
            comment "Unfold a definition"
         ,editParameters editFuns "Fold Definition" "subFunctionDef"
            subFunctionDef $ fileNamePar $ regionPar $
            comment "Folds against a definition"
         ,editParameters editFuns "Generative Fold of Definition" "genFold"
            genFold $ fileNamePar $ regionPar $
            comment "Replace an instance of the right hand side of a definition by the corresponding left hand side, creating a new recursive definition."
         ,editParameters editFuns "Select an equation for generative fold" "genFoldCache"
            genFoldCache $ fileNamePar $ positionPar $
            comment "Places an selcted equation into a cache for use by generative fold."
         ,editParameters editFuns "Convert pattern to use an as pattern" "refacAsPatterns"
            refacAsPatterns $ fileNamePar $ namePar "Name for Pattern: " $ regionPar $
            comment "Converts all appropriate patterns to use an as binding."

         ,editParameters editFuns "Unfold references to AS patterns" "refacUnfoldAsPatterns"
            refacUnfoldAsPatterns $ fileNamePar $ regionPar $
            comment "Converts all references to an as pattern to the actuall pattern."
         ,editParameters editFuns "Simplify Expression via Symbolic Evalutaion" "simplifyExpr"
            simplifyExpr $ fileNamePar $ regionPar $
            comment "Attempts to simplify a case expression."
         ]

       ,Menu "Definitions"
         [editParameters editFuns "Introduce new def" "introNewDef"
            introNewDef $ fileNamePar $ namePar "Name for new definition? " $ regionPar $
            comment "Introduce a new definition"
                  ,editParameters editFuns "Generalise def" "generaliseDef"
            generaliseDef $ fileNamePar $ namePar "name of new parameter? " $ regionPar $
            comment "Generalise a definition"

         ,editParameters editFuns "Remove def" "removeDef"
            removeDef $ fileNamePar $ positionPar $
            comment "Remove a definition if it is no used"
         ,editParameters editFuns "Duplicate def" "duplicateDef"
            duplicateDef $ fileNamePar $ namePar "Name for duplicate? " $ positionPar $
            comment "Duplicate a definition at the same level"
         ,editParameters editFuns "Add one parameter" "addOneParameter"
            addOneParameter $ fileNamePar $ namePar "name of new parameter? " $ positionPar $
            comment "Add parameter (default undefined)"
         ,editParameters editFuns "Rm one parameter" "rmOneParameter"
            rmOneParameter $ fileNamePar $ positionPar $
            comment "Remove unused parameter"
         ,editParameters editFuns "Move def to another module" "moveDefBtwMod"
            moveDefBtwMod $ fileNamePar $ namePar "name of the destination module? " $ positionPar $
            comment "Move a definition from one module to another module"
                  {- ,editParameters editFuns "Fold Constant Definition" "subConstantDef"
            subConstantDef $ fileNamePar $ positionPar $
            comment "Folds against a constant definition" -}

      {-   ,editParameters editFuns "Swap Arguments" "swapArgs"
            swapArgs $ fileNamePar $ positionPar $
            comment "Swap the first two arguments of a function"
          ,editParameters editFuns "From if to case" "ifToCase"
            ifToCase $ fileNamePar $ regionPar $
            comment "From if to case" -}
        ,editParameters editFuns "Converts guards to an if then else" "guardToIte"
            guardToIte $ fileNamePar $ positionPar $
            comment "Converts guards to an if then else"
        ,editParameters editFuns "Shortcut Deforestration" "deforest"
          deforest $ fileNamePar $
          comment "A (partial) implementation of the warm fusion algorithm"



          ]

       ,Menu "Import/Export"
         [editParameters editFuns "Clean imports" "cleanImports"
            cleanImports $ fileNamePar $
            comment "Tidy up the import list of the current module"
         ,editParameters editFuns "Make import explicit" "mkImpExplicit"
           mkImpExplicit $ fileNamePar $ positionPar $
           comment "Make the used entities explicit"
         ,editParameters editFuns "Add to export" "addToExport"
          addToExport $ fileNamePar $ positionPar $
          comment "Add an identifier to the export list"
         ,editParameters editFuns "Remove from export" "rmFromExport"
          rmFromExport $ fileNamePar $ positionPar $
          comment "Remove an identifier from the export list"
       {-  ,editParameters editFuns "Type Check" "refacType"
          refacType $ fileNamePar $
          comment "Type check the module" -}
         ]

       ,Menu "Data types"
         [editParameters editFuns "Add field labels" "addFieldLabels"
          addFieldLabels $ fileNamePar $ positionPar $
          comment "Add field labels to a data type declaration"
         ,editParameters editFuns "Add discriminators" "addDiscriminators"
          addDiscriminators $ fileNamePar $ positionPar $
          comment "Add discriminator functions to a data type declaration"
         ,editParameters editFuns "Add constructors" "addConstructors"
          addConstructors $ fileNamePar $ positionPar $
          comment "Add constructor functions to a data type declaration"
         ,editParameters editFuns "eliminate nested patterns" "elimNestedPatterns"
          elimPatterns  $ fileNamePar $ positionPar $
          comment "Eliminate nested pattern matchings"
         ,editParameters editFuns "eliminate patterns" "elimPatterns"
          elimPatterns  $ fileNamePar $ positionPar $
          comment "Eliminate pattern matchings"
         ,editParameters editFuns "Create an ADT module" "createADTMod"
            createADTMod $ fileNamePar $ positionPar $
            comment "Create an new ADT module"
         ,editParameters editFuns "From concrete to abstract data type" "fromAlgebraicToADT"
            createADTMod $ fileNamePar $ positionPar $
            comment "Transforms an algebraic data type to an ADT"
         ,editParameters editFuns "Add a new constructor to a data type" "refacAddCon"
            refacAddCon $ fileNamePar $ namePar "Enter text for constructor and parameters: " $ positionPar $ comment "Adds a new constructor to a data type"
         ,editParameters editFuns "Remove a constructor from a data type" "refacRmCon"
            refacRmCon $ fileNamePar $ positionPar $
            comment "Removes constructor from a data type"

         ,editParameters editFuns "Remove a field from a data type" "refacRemoveField"
            refacRemoveField $ fileNamePar $ namePar "Enter position of field to be removed: " $ positionPar $
            comment "Removes a field from a data type"
         ,editParameters editFuns "Add a field to a data type" "refacAddField"
            refacAddField $ fileNamePar $ namePar "Type of Field : " $ positionPar $
            comment "Adds a field to a data type"
         ]
     ,Menu "Duplicate Code"
         [
           editParameters editFuns "Duplicate Code Analysis" "duplicateCode"
           duplicateCode $ fileNamePar $ namePar "Clone Token Size: " $
           comment "Analysis a project for code duplication."
          ,editParameters editFuns "Transform Duplicate Code" "refacDupTrans"
           refacDupTrans $ fileNamePar $ regionPar $ comment "Transforms duplicate code"
          ,editParameters editFuns "Identify Class" "refacIdentify"
           refacIdentify $ fileNamePar $ regionPar $ comment "identifies a clone class"
         ]
      ,Menu "Parallel"
         [
           editParameters editFuns "Introduce Threshold" "refacIntroThreshold"
           refacIntroThreshold $ fileNamePar $ namePar "Enter threshold value: " $ namePar "Theshold parameter name: " $ regionPar $ comment "Turn parallelism on over a threshold limit"
          ,editParameters editFuns "Introduce Eval Monad" "refacEvalMon"
           refacEvalMon $ fileNamePar $ regionPar $ comment "Insert Eval Monad"
          ,editParameters editFuns "Activate an Evaluation Monad" "refacAddEvalMonCache"
           refacAddEvalMonCache $ fileNamePar $ regionPar $ comment "Activate Eval Monad"
          ,editParameters editFuns "Clear the active Evaluation Monad" "refacClearEvalCache"
           refacClearEvalCache $ fileNamePar $ comment "clear active eval monad"


         -- ,editParameters editFuns "Add pattern to runEval" "refacAddEvalMon"
         --  refacAddEvalMon $ fileNamePar $ regionPar $ comment "Add pattern to buffered Eval Monad"
         ]
       ,editParameters editFuns "undo" "undo"
          undo $
          comment "One step back in refactorer history"
       ]

-- refacAddEvalMon :: String -> Int -> Int -> Int -> Int -> IO ()
-- refacAddEvalMon f ls cs le ce = putStrLn $
--    ">refacAddEvalMon filename: "++f
--  ++" line: "++show ls++" column: "++show cs
--  ++" line: "++show le++" column: "++show ce
refacClearEvalCache :: String -> IO ()
refacClearEvalCache f = putStrLn $ ">refacClearEvalCache filename: " ++ f


refacAddEvalMonCache :: String -> Int -> Int -> Int -> Int -> IO ()
refacAddEvalMonCache f ls cs le ce = putStrLn $
    ">refacAddEvalMonCache filename: "++f
  ++" line: "++show ls++" column: "++show cs
  ++" line: "++show le++" column: "++show ce

refacIntroThreshold :: String -> String -> String -> Int -> Int -> Int -> Int -> IO ()
refacIntroThreshold f z n ls cs le ce = putStrLn $
    ">refacIntroThreshold filename: "++f ++ n ++ z
  ++" line: "++show ls++" column: "++show cs
  ++" line: "++show le++" column: "++show ce

refacEvalMon :: String -> Int -> Int -> Int -> Int -> IO ()
refacEvalMon f ls cs le ce = putStrLn $
    ">refacEvalMon filename: "++f
  ++" line: "++show ls++" column: "++show cs
  ++" line: "++show le++" column: "++show ce

refacDupTrans :: String -> Int -> Int -> Int -> Int -> IO ()
refacDupTrans f l c s n = putStrLn $ ">refacDupTrans: " ++ f++" line: "++show l++" column: "++show c

refacIdentify :: String -> Int -> Int -> Int -> Int -> IO ()
refacIdentify f l c s n = putStrLn $ ">refacIdentify: " ++ f++" line: "++show l++" column: "++show c


parseAnswers :: String -> IO ()
parseAnswers f =putStrLn "parseAnswers: "

new :: String -> IO ()
new f = putStrLn $ ">new filename: "++f

add :: String -> IO ()
add f = putStrLn $ ">add filename: "++f


chase :: String -> IO ()
chase d = putStrLn $ ">chase directory: "++d

files :: IO ()
files = putStrLn $ ">files "

undo :: IO ()
undo = putStrLn $ ">undo "

refacAddCon :: String -> String -> Int -> Int -> IO ()
refacAddCon f a l c = putStrLn $ ">refacAddCon: " ++ f ++ a
  ++ " line: " ++ show l ++ " column: " ++ show c


removeDef :: String -> Int -> Int -> IO ()
removeDef f l c = putStrLn $ ">removeDef filename: "++f++" line: "++show l++" column: "++show c

subFunctionDef :: String -> Int -> Int -> Int -> Int -> IO ()
subFunctionDef f l c s n= putStrLn $ ">subFunctionDef: "++f++" line: "++show l++" column: "++show c

{- subConstantDef :: String -> Int -> Int -> IO ()
subConstantDef f l c = putStrLn $ ">subConstantDef: "++f++" line: "++show l++" column :"++show c -}

duplicateDef :: String -> String -> Int -> Int -> IO ()
duplicateDef f n l c = putStrLn $ ">duplicateDef filename: "++f++" name for duplicate: "++show n++" line: "++show l++" column: "++show c

liftToTopLevel :: String -> Int -> Int -> IO ()
liftToTopLevel f l c = putStrLn $ ">liftToTopLevel filename: "++f++" line: "++show l++" column: "++show c

liftOneLevel :: String -> Int -> Int -> IO ()
liftOneLevel f l c = putStrLn $ ">liftOneLevel filename: "++f++" line: "++show l++" column: "++show c

demote :: String -> Int -> Int -> IO ()
demote f l c = putStrLn $ ">demote filename: "++f++" line: "++show l++" column: "++show c

rename :: String -> String -> Int -> Int -> IO ()
rename f n l c = putStrLn $ ">rename filename: "++f++" name: "++n++" line: "++show l++" column: "++show c

introNewDef :: String -> String -> Int -> Int -> Int -> Int -> IO ()
introNewDef f n ls cs le ce = putStrLn $
    ">introNewDef filename: "++f++" name: "++n
  ++" line: "++show ls++" column: "++show cs
  ++" line: "++show le++" column: "++show ce

unfoldDef :: String -> Int -> Int -> IO ()
unfoldDef f l c = putStrLn $ ">unfoldDef filename: "++f++" line: "++show l++" column: "++show c

addOneParameter :: String -> String -> Int -> Int -> IO ()
addOneParameter f p l c = putStrLn $ ">addOneParameter filename: "++f++" parameter name: "++p++" line: "++show l++" column: "++show c

rmOneParameter :: String -> Int -> Int -> IO ()
rmOneParameter f l c = putStrLn $ ">rmOneParameter filename: "++f++" line: "++show l++" column: "++show c

generaliseDef :: String -> String -> Int -> Int -> Int -> Int -> IO ()
generaliseDef f p ls cs le ce = putStrLn $
    ">generaliseDef filename: "++f++" parameter name: "++p
  ++" line: "++show ls++" column: "++show cs
  ++" line: "++show le++" column: "++show ce

moveDefBtwMod :: String -> String -> Int -> Int ->IO ()
moveDefBtwMod f p ls cs = putStrLn $
    ">moveDefBtwMod filename: "++f++" module name: "++p
  ++" line: "++show ls++" column: "++show cs

pwToPf  :: String ->Int -> Int -> Int -> Int -> IO ()
pwToPf  f ls cs le ce = putStrLn $
    ">tranlates from a pointfree to a pointwise expression: "++f
  ++" line: "++show ls++" column: "++show cs
  ++" line: "++show le++" column: "++show ce

guardToIte:: String -> Int -> Int -> IO ()
guardToIte f l c = putStrLn $
    ">Converts the guards into an if then else: "++f
      ++" line: "++show l
      ++" column: "++show c

deforest::String -> IO ()
deforest f = putStrLn $
    ">deforest fileName: " ++ f

cleanImports :: String->IO ()
cleanImports f= putStrLn $
    ">cleanImports filename: "++f

refacType :: String -> IO()
refacType f = putStrLn $
    ">typeCheck filename: " ++ f


refacTypeSig :: String -> IO ()
refacTypeSig f = putStrLn $
   ">refacTypeSig filename: " ++ f

mkImpExplicit :: String -> Int -> Int -> IO ()
mkImpExplicit f l c = putStrLn $ ">make the imported entities explicit: "++f++" line: "++show l++" column: "++show c

addToExport :: String -> Int -> Int -> IO ()
addToExport f l c = putStrLn $ ">add an identifier to the export list: "++f++" line: "++show l++" column: "++show c

rmFromExport ::String -> Int -> Int -> IO ()
rmFromExport f l c = putStrLn  $ ">remove an identifier from the export list: "++f++" line: "++show l++" column: "++show c

addFieldLabels ::String -> Int -> Int -> IO ()
addFieldLabels f l c = putStrLn  $ ">add field labels to a data type declaration: "++f++" line: "++show l++" column: "++show c

addDiscriminators ::String -> Int -> Int -> IO ()
addDiscriminators f l c = putStrLn  $ ">add discriminator functions to a data type declaration: "++f++" line: "++show l++" column: "++show c

addConstructors ::String -> Int -> Int -> IO ()
addConstructors f l c = putStrLn  $ ">add constructor functions to a data type declaration: "++f++" line: "++show l++" column: "++show c

elimPatterns ::String -> Int -> Int -> IO ()
elimPatterns f l c = putStrLn  $ ">eliminate pattern bindings: "++f++" line: "++show l++" column: "++show c

elimNestedPatterns ::String -> Int -> Int -> IO ()
elimNestedPatterns f l c = putStrLn  $ ">eliminate nested pattern bindings: "++f++" line: "++show l++" column: "++show c

createADTMod:: String -> Int -> Int ->IO ()
createADTMod f l c = putStrLn $
    ">create an ADT moule: "++f++" line: "++show l++" column: "++show c

fromAlgebraicToADT:: String -> Int -> Int ->IO ()
fromAlgebraicToADT f l c = putStrLn $
    ">transform an algebraic data type to an ADT: "++f++" line: "++show l++" column: "++show c


swapArgs:: String -> Int -> Int -> IO ()
swapArgs  f l c = putStrLn $ ">swapArgs filename: "++f++" line: "++show l++" column: "++show c


ifToCase :: String ->Int -> Int -> Int -> Int -> IO ()
ifToCase f ls cs le ce = putStrLn $
    ">from if to case: "++f
  ++" line: "++show ls++" column: "++show cs
  ++" line: "++show le++" column: "++show ce


refacRedunDec :: String -> Int -> Int -> Int -> Int -> IO ()
refacRedunDec f ls cs le ce = putStrLn $
    ">refacRedunDec: " ++ f
 ++ " line: " ++ show ls ++ " column: " ++ show cs
 ++ " line: " ++ show le ++ " column: " ++ show ce

refacDataNewType :: String -> Int -> Int -> IO ()
refacDataNewType f l c = putStrLn $
    ">refacDataNewType: " ++ f
 ++ " line: " ++ show l ++ " column: " ++ show c


refacSlicing :: String -> Int -> Int -> Int -> Int -> IO ()
refacSlicing f ls cs le ce = putStrLn $
    ">refacSlicing: " ++ f
 ++ " line: " ++ show ls ++ " column: " ++ show cs
 ++ " line: " ++ show le ++ " column: " ++ show ce

refacSlicTuple :: String -> Int -> Int -> String -> IO ()
refacSlicTuple f r c x= putStrLn $
   ">refacSlicTuple: " ++ f
 ++ " line: " ++ show r ++ " column: " ++ show c ++ x

refacDebug :: String -> Int -> Int -> IO ()
refacDebug f r c = putStrLn $
  ">refacDebug: " ++ f
 ++ " line: " ++ show r ++ " column: " ++ show c

refacMerge :: String -> String -> IO ()
refacMerge f x = putStrLn $
   ">refacMerge: " ++ f ++ x


refacCacheMerge :: String -> Int -> Int -> IO ()
refacCacheMerge f r c = putStrLn $
   ">refacCacheMerge: " ++ f
 ++ " line: " ++ show r ++ " column: " ++ show c

refacInstantiate :: String -> Int -> Int -> String -> IO ()
refacInstantiate f r c z= putStrLn $
   ">refacInstantiate: " ++ f
 ++ " line: " ++ show r ++ " column: " ++ show c ++ z

refacAsPatterns :: String -> String -> Int -> Int -> Int -> Int -> IO ()
refacAsPatterns f a ls cs le ce = putStrLn $
   ">refacAsPatterns: " ++ f ++ a
 ++ "line: " ++ show ls ++ " column: " ++ show cs
 ++ "line: " ++ show le ++ " column: " ++ show ce


refacUnfoldAsPatterns :: String -> Int -> Int -> Int -> Int -> IO ()
refacUnfoldAsPatterns f rs cs re ce = putStrLn $
   ">refacUnfoldAsPatterns: " ++ f
 ++ "line: " ++ show rs ++ " column: " ++ show cs
 ++ "line: " ++ show re ++ " column: " ++ show ce

letToWhere :: String -> Int -> Int -> IO ()
letToWhere f re ce = putStrLn $
   ">letToWhere: " ++ f
 ++ "line: " ++ show re ++ " column: " ++ show ce

whereToLet :: String -> Int -> Int -> IO ()
whereToLet f re ce = putStrLn $
   ">whereToLet: " ++ f
 ++ " line: " ++ show re ++ " column: " ++ show ce

duplicateCode :: String -> String -> IO ()
duplicateCode f a = putStrLn $
  " duplicateCode: " ++ f ++ a

refacRemoveField :: String -> String -> Int -> Int -> IO ()
refacRemoveField f n s e = putStrLn $
    ">refacRemoveField: " ++ f
 ++ "start: " ++ show s ++ "end: " ++ show e

refacAddField :: String -> String -> Int -> Int -> IO ()
refacAddField f n s e = putStrLn $
    ">refacAddField: " ++ f
 ++ n ++ "start: " ++ show s ++ "end: " ++ show e

refacRmCon :: String -> Int -> Int -> IO ()
refacRmCon f s e = putStrLn $
    ">refacRmCon: " ++ f
 ++ "start: " ++ show s ++ "end: " ++ show e

simplifyExpr :: String -> Int -> Int -> Int -> Int -> IO ()
simplifyExpr f ls cs le ce = putStrLn $
    ">simplifyExpr filename: "++f
  ++" line: "++show ls++" column: "++show cs
  ++" line: "++show le++" column: "++show ce

genFold :: String -> Int -> Int -> Int -> Int -> IO ()
genFold f ls cs le ce = putStrLn $
    ">genFold filename: "++f
  ++" line: "++show ls++" column: "++show cs
  ++" line: "++show le++" column: "++show ce

introPattern :: String -> Int -> Int -> IO ()
introPattern f s e = putStrLn $
    "introPattern: " ++ f
 ++ "start: " ++ show s ++ "end: " ++ show e

introCase :: String -> Int -> Int -> IO ()
introCase f s e = putStrLn $
    "introPattern: " ++ f
 ++ "start: " ++ show s ++ "end: " ++ show e

genFoldCache :: String -> Int -> Int -> IO ()
genFoldCache f s e = putStrLn $
    "genFoldCache: " ++ f
 ++ "start: " ++ show s ++ "end: " ++ show e

foldPattern :: String -> String -> Int -> Int -> Int -> Int -> IO ()
foldPattern f n ls cs le ce = putStrLn $
    ">foldPattern filename: "++f++" name: "++n
  ++" line: "++show ls++" column: "++show cs
  ++" line: "++show le++" column: "++show ce
---------------------------------------------------------------------------

main = cmdLoop

-- foreign export ccall cmdLoop :: IO ()

cmdLoop :: IO ()
cmdLoop = getArgs >>= doCmd
  {-
  l <- getLine
  doCmd $ words l
  cmdLoop
  -}
  where
    doCmd []         = exitWith ExitSuccess
    doCmd (arg:args) =
        case lookup arg [(entry,c) | (Entry entry name c) <- cmds defaultEditor] of
          Just c  -> cmd c () args
          Nothing | arg=="help"               -> help
          Nothing | arg=="pfeRefactoringCmds" -> pfeRefactoringCmds
          Nothing | arg=="vim"                -> gen_interface Vim.editor (cmds Vim.editor)
          Nothing | arg=="emacs"              -> gen_interface Emacs.editor (cmds Emacs.editor)
          _ -> putStrLn $ "command not found:"++show arg
