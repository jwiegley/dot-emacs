module ParseProgram where

import HsModule
import HsConstants(prelude_mod)
import SrcLoc(loc0)
--import HsName
import NamesEntities
import ParseMonad(parseFile)
import Unlit(readHaskellFile)
import ParserOptions

import WorkModule(analyzeModules,WorkModuleI(..))
import PPModules
import TypedIds(NameSpace(..),IdTy(..),namespace)

import ReAssoc(getInfixes)
import ReAssocModule
--import ReAssocBaseStruct -- instance for HsModule

import MUtils((@@),( # ), mapFst)
import Lift

-- Parse a program, analyze module dependencies and adjust infix
-- applications in accordance with operator precedences:
-- parseProgram :: ... => PM (HsModule ds) -> [FilePath] ->
--                        ([[HsModule ds]],[(Module,WorkModule)])
parseProgram files = parseProgram' flags0 files
parseProgram' flags parseMod files =
  rewriteProgram # analyzeFiles' flags parseMod files

analyzeFiles parseMod = analyzeFiles' flags0 parseMod
analyzeFiles' flags parseMod =
  lift . analyzeModules'' (prel flags) @@ parseSourceFiles (cpp flags) parseMod

analyzeModules' x = analyzeModules'' True x
analyzeModules'' prel x = analyzeModules . map (optAddPrelude prel)  $x

parseSourceFiles cpp parseMod = mapM (parseSourceFile cpp parseMod)

parseSourceFile cpp parseMod path =
    parseFile parseMod path =<< readHaskellFile cpp path

rewriteProgram (modss,wms) =
    ((map.map) reAssocMod modss,wms)
  where
    origOps = (concatMap.map) infixDecls modss
    infixDecls mod = (hsModName mod,mapFst getQualified (getInfixes mod))

    reAssocMod mod = reAssocModule wm origOps mod
       where Just wm = lookup (hsModName mod) wms
