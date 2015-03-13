module AST4ModSys where

import qualified HsModule as Hs
import HsModuleMaps()
import HsIdent(getHSName)
import qualified Ents (Ent(Ent))
import DefinedNames(DefinedNames(definedNames))
--import TypedIds (NameSpace(..))

import Relations
import Names
import ModSysAST
import HasBaseName

import Products((><))

-- added by Huiqing Li
import UniqueNames
import PNT
import Data.Maybe
import SourceNames
import SrcLoc1
import HsName hiding (ModuleName)
import HsIdent
import PosName
-------------------------

--toMod :: DefinedNames QName ds => Hs.HsModuleI QName ds -> Module
toMod (Hs.HsModule s m exp imps ds) 
  = Module {
      modName       = getBaseName m,
      modExpList    = map toExpListEntry `fmap` exp,
      modImports    = toImport `map` imps,
      modDefines    = listToRel (toEnt `map` defs)
    }
    where
    defs            = map (fmap getQualified >< fmap getQualified) 
                    $ definedNames ds
    toEnt (x,y)     = (getHSName x,Ents.Ent (getBaseName m) x y)


-- exports
--toExpListEntry :: Hs.HsExportSpecI QName -> ExpListEntry 
toExpListEntry x =
  case x of
    Hs.EntE i -> EntExp (toEnt getQualified i)
    Hs.ModuleE m -> ModuleExp (getBaseName m)


-- imports 
--toImport :: Hs.HsImportDeclI QName -> Import 
toImport (Hs.HsImportDecl _ m qualified as spec) 
  = Import {
      impSource     = getBaseName m,
      impQualified  = qualified,
      impAs         = getBaseName (maybe m id as),
      impHiding     = hiding,
      impList       = xs
    }
    where
    (hiding, xs) = cvt spec
    cvt Nothing = (True, [])
    cvt (Just (hiding,specs)) = (hiding, toImpListEntry `map` specs)


--toImpListEntry :: Hs.HsImportSpecI QName -> EntSpec Name
toImpListEntry = toEnt id . fmap f
  where
    f = getQualified -- or perhaps signal an error if something is qualified?

--toEnt :: Hs.EntSpec i -> EntSpec i
toEnt unq x =
  case x of
    Hs.Var i           -> Ent i Nothing
    Hs.Abs i           -> Ent i Nothing
    Hs.AllSubs i       -> Ent i (Just AllSubs)
    Hs.ListSubs i js   -> Ent i (Just $ Subs (map (unq.getHSName) js))



------- Added by Huiqing Li -----------------

-- imports 
toImport' :: Hs.HsImportDeclI ModName PNT -> Import 
toImport' (Hs.HsImportDecl _  m qualified as spec) 
  = Import {
      impSource     = m,
      impQualified  = qualified,
      impAs         = maybe m id as,
      impHiding     = hiding,
      impList       = xs
    }
    where
    (hiding, xs) = cvt spec
    cvt Nothing = (True, [])
    cvt (Just (hiding,specs)) = (hiding, toImpListEntry' `map` specs)

pNTtoName=hsNameToName.pNTtoHsName

pNTtoHsName::PNT->QName
pNTtoHsName (PNT pn@(PN i orig) _ _)
  = let loc=(fromMaybe loc0 . optLoc') pn
    in (SN i loc)
  where
     optLoc' (PN i o) 
      = case o of
         G m n (N optp) -> optp
         --  I m p -> Just p
         S p -> Just p
         D n (N optp) -> optp
         _ -> Nothing

hsNameToName::QName ->Names.Name
hsNameToName (SN (Qual _ id) l) =(SN id l)
hsNameToName (SN (UnQual id) l) =(SN id l) 

hsIdentToHsName (HsVar pnt) =pNTtoHsName pnt 
hsIdentToHsName (HsCon pnt) =pNTtoHsName pnt

toImpListEntry' :: Hs.HsImportSpecI PNT -> EntSpec Name
toImpListEntry' = toEnt' pNTtoName. fmap f
  where
    f = getQualified -- or perhaps signal an error if something is qualified?


--toEnt :: Hs.EntSpec i -> EntSpec i
toEnt' unq x =
  case x of
    Hs.Var i           -> Ent (pNTtoName i) Nothing
    Hs.Abs i           -> Ent (pNTtoName i) Nothing
    Hs.AllSubs i       -> Ent (pNTtoName i) (Just AllSubs)
    Hs.ListSubs i js   -> Ent (pNTtoName i) (Just $ Subs (map (hsNameToName.hsIdentToHsName) js))

toExpListEntry' :: Hs.HsExportSpecI (PosName.ModuleName) PNT ->ExpListEntry
toExpListEntry' x =
  case x of
    Hs.EntE i -> EntExp (toEnt getQualified (fmap pNTtoHsName i))
    Hs.ModuleE (SN m _) -> ModuleExp m

