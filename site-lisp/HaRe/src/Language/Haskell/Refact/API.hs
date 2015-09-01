-- | This module should provide all that is required to write further
-- refactorings.
-- NOTE: it is currently unstable, and may change without notice on minor version number bumps
module Language.Haskell.Refact.API
 (
 -- * from `Language.Haskell.Refact.Utils.Monad`
         ParseResult
       , VerboseLevel(..)
       , RefactSettings(..)
       , TargetModule
       , RefactFlags(..)
       , StateStorage(..)

       -- ** The GHC Monad
       , RefactGhc
       , runRefactGhc
       , getRefacSettings
       , defaultSettings
       , logSettings
       , initGhcSession

       , loadModuleGraphGhc
       , ensureTargetLoaded
       , canonicalizeGraph

       , logm

 -- * from `Language.Haskell.Refact.Utils.Utils`

       -- ** Managing the GHC / project environment
       -- , loadModuleGraphGhc
       , getModuleGhc
       , parseSourceFileGhc
       , activateModule
       , getModuleDetails

       -- ** The bits that do the work
       , runRefacSession
       , applyRefac
       , refactDone
       , ApplyRefacResult
       , RefacSource(..)

       , update
       , fileNameToModName
       , fileNameFromModSummary
       , getModuleName
       , clientModsAndFiles
       , serverModsAndFiles


 -- * from `Language.Haskell.Refact.Utils.MonadFunctions`

       -- ** Conveniences for state access

       -- , fetchToksFinal
       , fetchLinesFinal
       , fetchOrigToks
       , fetchToks -- Deprecated
       , getTypecheckedModule
       , getRefactStreamModified
       , getRefactInscopes
       , getRefactRenamed
       , putRefactRenamed
       , getRefactParsed
       , putParsedModule
       , clearParsedModule
       , getRefactFileName

       -- ** TokenUtils API
       , replaceToken
       , putToksForSpan
       , putDeclToksForSpan
       , getToksForSpan
       -- , getToksForSpanNoInv
       -- , getToksForSpanWithIntros
       , getToksBeforeSpan
       , putToksForPos
       , addToksAfterSpan
       , addToksAfterPos
       , putDeclToksAfterSpan
       , removeToksForSpan
       , removeToksForPos
       , syncDeclToLatestStash
       , indentDeclAndToks

       -- ** LayoutUtils API

       -- ** For debugging
       , drawTokenTree
       , drawTokenTreeDetailed
       , getTokenTree
       , showLinesDebug

       -- ** State flags for managing generic traversals
       , getRefactDone
       , setRefactDone
       , clearRefactDone

       , setStateStorage
       , getStateStorage

       -- , logm

       , updateToks
       , updateToksWithPos

 -- * from `Language.Haskell.Refact.Utils.LocUtils`

                     , SimpPos,unmodified,modified
                     , simpPos0
                     , nullSrcSpan
                     -- , showToks
                     , whiteSpaceTokens
                     , realSrcLocFromTok
                     , isWhite
                     , notWhite
                     , isWhiteSpace
                     , isWhiteSpaceOrIgnored
                     , isIgnored
                     , isIgnoredNonComment
                     {-
                     ,isNewLn,isCommentStart -},isComment {-,
                     isNestedComment-},isMultiLineComment {-,isOpenBracket,isCloseBracket, -}
                     ,isOpenSquareBracket,isCloseSquareBracket {- ,isOpenBrace,isConid,
                     isLit,isWhereOrLet,isWhere,isLet-},isIn {- ,isCase,isDo,isIf,isForall,
                     isHiding,isModule-} ,isComma {-,isEqual,isLambda,isIrrefute -},isBar --,isMinus,
                     ,endsWithNewLn,startsWithNewLn,hasNewLn {- ,startsWithEmptyLn,
                     lastNonSpaceToken,firstNonSpaceToken -} ,compressPreNewLns,compressEndNewLns

                     , lengthOfLastLine
                     , getToks
                     -- , replaceToks,replaceTok
                     ,replaceTokNoReAlign,deleteToks,doRmWhites -- ,doAddWhites
                     , srcLocs
                     , getSrcSpan, getAllSrcLocs
                     -- , ghcSrcLocs -- Test version
                     -- , getLocatedStart
                     -- , getLocatedEnd
                     , getBiggestStartEndLoc
                     {-
                     , getStartEndLoc2,
                     startEndLoc,extendBothSides -},extendForwards,extendBackwards
                     , startEndLocIncFowComment{- ,startEndLocIncFowNewLn -}
                     , startEndLocIncComments, startEndLocIncComments'
                     , tokenise
                     , basicTokenise
                     , prettyprintPatList
                     , groupTokensByLine
                     , toksOnSameLine
                     , addLocInfo
                     -- , getIndentOffset
                     , getLineOffset
                     -- , splitToks
                     -- , splitOnNewLn
                     {-
                     , insertComments,
                     extractComments, insertTerms
                     -}
                     , tokenCol
                     , tokenColEnd
                     , tokenRow
                     , tokenPos
                     , tokenPosEnd
                     , tokenSrcSpan
                     , tokenCon
                     , increaseSrcSpan
                     , getGhcLoc
                     , getGhcLocEnd
                     , getLocatedStart
                     , getLocatedEnd
                     , getStartEndLoc
                     , startEndLocGhc
                     , realSrcLocEndTok
                     , fileNameFromTok
                     , splitToks
                     , emptyList, nonEmptyList
                     -- , divideComments
                     , notWhiteSpace
                     , isDoubleColon
                     , isEmpty
                     , isWhereOrLet
                     , isWhere
                     , isLet
                     , isElse
                     , isThen
                     , isOf
                     , isDo
                     , getIndentOffset
                     , splitOnNewLn
                     , tokenLen
                     , newLnToken
                     -- , newLinesToken
                     -- , monotonicLineToks
                     , reSequenceToks
                     , mkToken
                     , mkZeroToken
                     , markToken
                     , isMarked
                     , addOffsetToToks
                     , matchTokenPos
                     , rmOffsetFromToks

 -- * from `Language.Haskell.Refact.Utils.TypeSyn`
    , InScopes
    , PosToken
    , ghead
    , glast
    , gtail
    , gfromJust

 -- * from `Language.Haskell.Refact.Utils.TypeUtils`

 -- ** Program Analysis
    -- ** Imports and exports
   , inScopeInfo, isInScopeAndUnqualified, isInScopeAndUnqualifiedGhc, inScopeNames
   -- , hsQualifier, {-This function should be removed-} rmPrelude
   {-,exportInfo -}, isExported, isExplicitlyExported, modIsExported

    -- *** Variable analysis
    , isFieldName
    , isClassName
    , isInstanceName
    ,hsPNs -- ,hsDataConstrs,hsTypeConstrsAndClasses, hsTypeVbls
    {- ,hsClassMembers -} , hsBinds, replaceBinds, HsValBinds(..)
    ,isDeclaredIn
    ,hsFreeAndDeclaredPNsOld, hsFreeAndDeclaredNameStrings
    ,hsFreeAndDeclaredPNs
    ,hsFreeAndDeclaredGhc
    ,getDeclaredTypes
    ,getFvs, getFreeVars, getDeclaredVars -- These two should replace hsFreeAndDeclaredPNs

    ,hsVisiblePNs {- , hsVisiblePNsOld -}, hsVisibleNames
    ,hsFDsFromInside, hsFDNamesFromInside
    ,hsVisibleDs

    -- *** Property checking
    ,isVarId,isConId,isOperator,isTopLevelPN,isLocalPN,isNonLibraryName -- ,isTopLevelPNT
    ,isQualifiedPN {- , isFunName, isPatName-}, isFunOrPatName {-,isTypeCon-} ,isTypeSig
    ,isFunBindP,isFunBindR,isPatBindP,isPatBindR,isSimplePatBind
    ,isComplexPatBind,isFunOrPatBindP,isFunOrPatBindR -- ,isClassDecl,isInstDecl -- ,isDirectRecursiveDef
    ,usedWithoutQualR {- ,canBeQualified, hasFreeVars -},isUsedInRhs
    ,findPNT,findPN,findAllNameOccurences
    ,findPNs, findEntity, findEntity'
    ,sameOccurrence
    , findIdForName
    , getTypeForName
    ,defines, definesP,definesTypeSig -- , isTypeSigOf
    -- ,HasModName(hasModName), HasNameSpace(hasNameSpace)
    ,sameBind
    {- ,usedByRhs -},UsedByRhs(..)

    -- *** Modules and files
    -- ,clientModsAndFiles,serverModsAndFiles,isAnExistingMod
    -- ,fileNameToModName, strToModName, modNameToStr
    , isMainModule
    , getModule

    -- *** Locations
    ,defineLoc, useLoc, locToExp  -- , getStartEndLoc
    ,locToName, locToRdrName
    ,getName

 -- * Program transformation
    -- *** Adding
    ,addDecl, addItemsToImport, addHiding --, rmItemsFromImport, addItemsToExport
    ,addParamsToDecls, addActualParamsToRhs {- , addGuardsToRhs-}, addImportDecl, duplicateDecl -- , moveDecl
    -- *** Removing
    ,rmDecl, rmTypeSig, rmTypeSigs -- , commentOutTypeSig, rmParams
    -- ,rmItemsFromExport, rmSubEntsFromExport, Delete(delete)

    -- *** Updating
    -- ,Update(update)
    {- ,qualifyPName-},rmQualifier,qualifyToplevelName,renamePN {- ,replaceNameInPN -},autoRenameLocalVar

    -- ** Miscellous
    -- *** Parsing, writing and showing
    {- ,parseSourceFile,writeRefactoredFiles-}, showEntities,showPNwithLoc -- , newProj, addFile, chase
    -- *** Locations
    -- ,toRelativeLocs, rmLocs
    -- *** Default values
   ,defaultPN {- ,defaultPNT -},defaultName {-,defaultModName-},defaultExp -- ,defaultPat, defaultExpUnTyped


    -- *** Identifiers, expressions, patterns and declarations
    ,ghcToPN,lghcToPN, expToName
    ,nameToString
    {- ,expToPNT, expToPN, nameToExp,pNtoExp -},patToPNT {- , patToPN --, nameToPat -},pNtoPat
    {- ,definingDecls -}, definedPNs
    , definingDeclsNames, definingDeclsNames', definingSigsNames
    , definingTyClDeclsNames
    , allNames
    -- ,simplifyDecl

    -- *** Others
    , mkRdrName,mkNewGhcName,mkNewName,mkNewToplevelName

    -- The following functions are not in the the API yet.
    , causeNameClashInExports {- , inRegion , unmodified -}

    , removeOffset

    -- ** Typed AST traversals (added by CMB)
    -- ** Miscellous
    -- ,removeFromInts, getDataName, checkTypes, getPNs, getPN, getPNPats, mapASTOverTAST

    -- ** Debug stuff
    , getDeclAndToks, getSigAndToks
    , getToksForDecl, removeToksOffset -- ++AZ++ remove this after debuggging
    , getParsedForRenamedLPat
    , getParsedForRenamedName
    , getParsedForRenamedLocated
    -- , allPNT
    --  , allPNTLens
    -- , newNameTok
    , stripLeadingSpaces
    -- , lookupNameGhc

 -- ** from `Language.Haskell.Refact.Utils.GhcUtils`
    -- ** SYB versions
    , everythingButStaged
    , somethingStaged
    , everythingStaged
    , somewhereMStaged
    , somewhereMStagedBu
    , everywhereMStaged
    , everywhereMStaged'
    , everywhereStaged
    , everywhereStaged'
    , onelayerStaged
    , listifyStaged

    -- *** SYB Utility
    , checkItemRenamer

    -- ** Strafunski StrategyLib versions
    , full_tdTUGhc
    , stop_tdTUGhc
    , stop_tdTPGhc
    , allTUGhc'
    , once_tdTPGhc
    , once_buTPGhc
    , oneTPGhc
    , allTUGhc

    -- *** Strafunski utility
    , checkItemStage'
    , checkItemRenamer'

    -- ** Scrap Your Zipper versions
    , zeverywhereStaged
    , zopenStaged
    , zsomewhereStaged
    , transZ
    , transZM
    , zopenStaged'
    , ztransformStagedM
    -- *** SYZ utilities
    , checkZipperStaged
    , upUntil
    , findAbove

 -- * from `Language.Haskell.Refact.Utils.GhcVersionSpecific`
  , showGhc
  , prettyprint
  , prettyprint2
  , ppType
  , lexStringToTokens
  , getDataConstructors
  , setGhcContext

 -- * from `Language.Haskell.Refact.Utils.TokenUtils`
 , Positioning(..)
 , reIndentToks
 , ghcSrcSpanToForestSpan

 -- * Span conversion functions
 , gs2f,f2gs
 , gs2ss,ss2gs
 ) where

import Language.Haskell.Refact.Utils.Binds
import Language.Haskell.Refact.Utils.GhcUtils
import Language.Haskell.Refact.Utils.GhcVersionSpecific
import Language.Haskell.Refact.Utils.LocUtils
import Language.Haskell.Refact.Utils.Monad
import Language.Haskell.Refact.Utils.MonadFunctions
import Language.Haskell.Refact.Utils.TokenUtils
import Language.Haskell.Refact.Utils.TypeSyn
import Language.Haskell.Refact.Utils.TypeUtils
import Language.Haskell.Refact.Utils.Utils

import Language.Haskell.TokenUtils.Types
import Language.Haskell.TokenUtils.TokenUtils
import Language.Haskell.TokenUtils.Utils
import Language.Haskell.TokenUtils.GHC.Layout
