-- refactoring commands added to pfe command interpreter
-- this file is generated from GenEditorInterfaces.hs
-- by calling the executable as follows:
--   editors/GenEditorInterfaces pfeRefactoringCmds > refactorer/PfeRefactoringCmds.hs

module PfeRefactoringCmds where

import PfeParse
import RefacMoveDef
import RefacRenaming
import RefacDupDef
import RefacCacheMerge
import RefacNewDef
import RefacSlicTuple
import RefacMerge
import RefacRmDef
import RefacAddRmParam
import RefacGenDef
import RefacMvDefBtwMod
import DuplicateCode
import RefacCleanImps
import ParseAnswers
import RefacAddCon
import RefacTypeSig
import RefacADT
import RefacSwapArgs
import RefacRedunDec
import RefacSlicing
import RefacDeForest
import RefacUnGuard
import RefacFunDef
import RefacAsPatterns
import RefacUnfoldAsPatterns
import RefacInstantiate
import RefacDupTrans
import RefacRemoveField
import RefacAddField
import RefacLetWhere
import RefacRmCon
import RefacWhereLet
import RefacIntroPattern
import RefacSimplify
import RefacGenFold
import RefacGenCache
import RefacIdentify
-- ++AZ++ Next three are new since 0.6.0.2
import RefacEvalMon
import RefacAddEvalMonCache
import RefacIntroThreshold

{-
pfeRefactoringCmds ::
  [(String,          -- name of refactoring
    (CmdLineParser3.P
       (WithState
          (PFE0State
             (SN [Char]) Names.QName ds (PFE2.PFE2Info (SN [Char]), ext))
          IO
          ()),
     String          -- Help text
    ))]
-}  
pfeRefactoringCmds =
  [
   -- menu Names/Scopes
   ("rename",(args " <fileName> <name (New name? )> <line> <column>" rename, " Rename a variable name"))
  ,("liftToTopLevel",(args " <fileName> <line> <column>" liftToTopLevel, " Lift a local declaration to top level"))
  ,("liftOneLevel",(args " <fileName> <line> <column>" liftOneLevel, " Lift a local declaration one level up"))
  ,("demote",(args " <fileName> <line> <column>" demote, " Demote a declaration to where it is used"))
  ,("refacTypeSig",(args " <fileName>" refacTypeSig, " Generates type signatures for top-level definitions using GHC."))
  ,("parseAnswers",(args " <fileName>" parseAnswers, " Read in an answer"))
  ,("letToWhere",(args " <fileName> <line> <column>" letToWhere, " Converts a let expression into a where equation."))
  ,("whereToLet",(args " <fileName> <line> <column>" whereToLet, " Converts a where equation into a let expression"))
  ,("introPattern",(args " <fileName> <line> <column>" introPattern, " Replace variable with exhaustive set of patterns"))
  ,("introCase",(args " <fileName> <line> <column>" introCase, " Introduction of cases analysis via a pattern variable"))
  ,("foldPattern",(args " <fileName> <name (Name of pattern variable: )> <line> <column> <line> <column>" foldPattern, " Folds a sub-expression against a pattern variable"))
   -- menu Slicing
  ,("refacRedunDec",(args " <fileName> <line> <column> <line> <column>" refacRedunDec, " Removes redundant declarations in a where clause or expression"))
  ,("refacSlicing",(args " <fileName> <line> <column> <line> <column>" refacSlicing, " Slices a subexpression"))
  ,("refacSlicTuple",(args " <fileName> <line> <column> <name (Elements to slice: (A for all; (x,_x,_) for some): )>" refacSlicTuple, " slices a definition which returns a tuple"))
  ,("refacMerge",(args " <fileName> <name (Name for new definition: )>" refacMerge, " Merges multiple definitions to form one single definition."))
  ,("refacCacheMerge",(args " <fileName> <line> <column>" refacCacheMerge, " Adds a definition to the cache for merging."))
  ,("refacInstantiate",(args " <fileName> <line> <column> <name (patterns: )>" refacInstantiate, " Instantiates patterns in a generalised function clause"))
   -- menu Fold/Unfold
  ,("unfoldDef",(args " <fileName> <line> <column>" unfoldDef, " Unfold a definition"))
  ,("subFunctionDef",(args " <fileName> <line> <column> <line> <column>" subFunctionDef, " Folds against a definition"))
  ,("genFold",(args " <fileName> <line> <column> <line> <column>" genFold, " Replace an instance of the right hand side of a definition by the corresponding left hand side, creating a new recursive definition."))
  ,("genFoldCache",(args " <fileName> <line> <column>" genFoldCache, " Places an selcted equation into a cache for use by generative fold."))
  ,("refacAsPatterns",(args " <fileName> <name (Name for Pattern: )> <line> <column> <line> <column>" refacAsPatterns, " Converts all appropriate patterns to use an as binding."))
  ,("refacUnfoldAsPatterns",(args " <fileName> <line> <column> <line> <column>" refacUnfoldAsPatterns, " Converts all references to an as pattern to the actuall pattern."))
  ,("simplifyExpr",(args " <fileName> <line> <column> <line> <column>" simplifyExpr, " Attempts to simplify a case expression."))
   -- menu Definitions
  ,("introNewDef",(args " <fileName> <name (Name for new definition? )> <line> <column> <line> <column>" introNewDef, " Introduce a new definition"))
  ,("generaliseDef",(args " <fileName> <name (name of new parameter? )> <line> <column> <line> <column>" generaliseDef, " Generalise a definition"))
  ,("removeDef",(args " <fileName> <line> <column>" removeDef, " Remove a definition if it is no used"))
  ,("duplicateDef",(args " <fileName> <name (Name for duplicate? )> <line> <column>" duplicateDef, " Duplicate a definition at the same level"))
  ,("addOneParameter",(args " <fileName> <name (name of new parameter? )> <line> <column>" addOneParameter, " Add parameter (default undefined)"))
  ,("rmOneParameter",(args " <fileName> <line> <column>" rmOneParameter, " Remove unused parameter"))
  ,("moveDefBtwMod",(args " <fileName> <name (name of the destination module? )> <line> <column>" moveDefBtwMod, " Move a definition from one module to another module"))
  ,("guardToIte",(args " <fileName> <line> <column>" guardToIte, " Converts guards to an if then else"))
  ,("deforest",(args " <fileName>" deforest, " A (partial) implementation of the warm fusion algorithm"))
   -- menu Import/Export
  ,("cleanImports",(args " <fileName>" cleanImports, " Tidy up the import list of the current module"))
  ,("mkImpExplicit",(args " <fileName> <line> <column>" mkImpExplicit, " Make the used entities explicit"))
  ,("addToExport",(args " <fileName> <line> <column>" addToExport, " Add an identifier to the export list"))
  ,("rmFromExport",(args " <fileName> <line> <column>" rmFromExport, " Remove an identifier from the export list"))
   -- menu Data types
  ,("addFieldLabels",(args " <fileName> <line> <column>" addFieldLabels, " Add field labels to a data type declaration"))
  ,("addDiscriminators",(args " <fileName> <line> <column>" addDiscriminators, " Add discriminator functions to a data type declaration"))
  ,("addConstructors",(args " <fileName> <line> <column>" addConstructors, " Add constructor functions to a data type declaration"))
  ,("elimNestedPatterns",(args " <fileName> <line> <column>" elimNestedPatterns, " Eliminate nested pattern matchings"))
  ,("elimPatterns",(args " <fileName> <line> <column>" elimPatterns, " Eliminate pattern matchings"))
  ,("createADTMod",(args " <fileName> <line> <column>" createADTMod, " Create an new ADT module"))
  ,("fromAlgebraicToADT",(args " <fileName> <line> <column>" fromAlgebraicToADT, " Transforms an algebraic data type to an ADT"))
  ,("refacAddCon",(args " <fileName> <name (Enter text for constructor and parameters: )> <line> <column>" refacAddCon, " Adds a new constructor to a data type"))
  ,("refacRmCon",(args " <fileName> <line> <column>" refacRmCon, " Removes constructor from a data type"))
  ,("refacRemoveField",(args " <fileName> <name (Enter position of field to be removed: )> <line> <column>" refacRemoveField, " Removes a field from a data type"))
  ,("refacAddField",(args " <fileName> <name (Type of Field : )> <line> <column>" refacAddField, " Adds a field to a data type"))
   -- menu Duplicate Code
  ,("duplicateCode",(args " <fileName> <name (Clone Token Size: )>" duplicateCode, " Analysis a project for code duplication."))
  ,("refacDupTrans",(args " <fileName> <line> <column> <line> <column>" refacDupTrans, " Transforms duplicate code"))
  ,("refacIdentify",(args " <fileName> <line> <column> <line> <column>" refacIdentify, " identifies a clone class"))

-- ++AZ++ these are new since 0.6.0.2
   -- menu Parallel
  ,("refacIntroThreshold",(args " <fileName> <name (Enter threshold value: )> <name (Theshold parameter name: )> <line> <column> <line> <column>" refacIntroThreshold, " Turn parallelism on over a threshold limit"))
  ,("refacEvalMon",(args " <fileName> <line> <column> <line> <column>" refacEvalMon, " Insert Eval Monad"))
  ,("refacAddEvalMonCache",(args " <fileName> <line> <column> <line> <column>" refacAddEvalMonCache, " Activate Eval Monad"))
  ,("refacClearEvalCache",(args " <fileName>" refacClearEvalCache, " clear active eval monad"))
  ]
