{-# OPTIONS_GHC -cpp  #-}
module WorkModule(WorkModuleI(..),Ent(..),ExpRel,
		  analyzeModules, -- obsolete
		  mkWM,inscpList,analyzeSCM,readRel,showRel
		  ) where

import Modules
import Data.Maybe(fromMaybe,fromJust)
--import Names
import Ents

import DefinedNames
import Relations
import CheckModules
import SCMs
import ModSysAST
import AST4ModSys(toMod)

import PrettyPrint
import PPModules

import MUtils(mapFst,mapSnd)

#if __GLASGOW_HASKELL__ >= 604 
import qualified Data.Set as S hiding (map)

elemsS = S.elems
#else
import qualified Sets as S

elemsS = S.setToList
#endif


-- a user of the module system


type ExpRel n = Rel n (Ent n)

data WorkModuleI i n = WorkModuleI
    { inscpRel      :: Rel i (Ent n)
    , expRel        :: ExpRel n
    , inScope       :: i -> [Ent n]
    , inScopeDom    :: [i]
    , inScopeRng    :: [Ent n]
    , exports       :: [(n, Ent n)]
    }
inscpList = relToList . inscpRel

--instance (Ord i, Ord n, Read i, Read n) => Read (WorkModuleI i n) where
--    readsPrec p xs = [ (mkWM p,ys) | (p,ys) <- readsPrec p xs]

instance (Show i, Show n) => Show (WorkModuleI i n) where
    showsPrec p wm = showsPrec p (inscpRel wm, expRel wm)

mkWM (i,e) = WorkModuleI 
        { inscpRel      = i
        , expRel        = e

        , inScope       = applyRel i
        , inScopeDom    = elemsS (dom i)
        , inScopeRng    = elemsS (rng i)
        , exports       = relToList e
        }

instance (Printable i, Printable n) => Printable (WorkModuleI i n) where
    ppi wm  = text "in scope:" 
            $$ ppRel ((\x -> (x,inScope wm x)) `map` inScopeDom wm)
            $$ "exports:"
            $$ ppRel (exports wm)


type ExportRel n = Rel n (Ent n)
{-
analyzeSCM :: 
    (QualNames i ModuleName n, DefinedNames i ds, Eq n) => 
    [(ModuleName, ExportRel n)] -> 
    [HsModuleI i ds] -> 
    Either 
        [(ModuleName,[ModSysErr i ModuleName n (Ent n)])] 
        [(ModuleName,WorkModuleI i n)]
-}
analyzeSCM exports_from_earlier scms 
    | not (null errs)   = Left errs
    | otherwise         = Right newwms
    where
    mods        = toMod `map` scms
    newwms'     = mods `zip` map mkWM (computeInsOuts otherExps mods)
    newwms      = mapFst modName newwms'
    otherExps m = fromMaybe emptyRel $ lookup m exports_from_earlier

    all_exports = mapSnd expRel newwms++exports_from_earlier
    expsOf  m   = lookup m all_exports
    errs        = [ (modName m, es) | (m,wm) <- newwms', 
                    let es = chkModule expsOf (inscpRel wm) m, not (null es) ]

    --fromJust' = fromMaybe (error "WorkModule.analyzeSCM")

-- obsolete function
analyzeModules ms 
    | not $ all null errs   = Left $ reportErrs errs
    | otherwise             = Right (scms, wms)
    where

    scms    = scMods ms
    scmods  = map toMod `map` scms 
    
    mods    = concat scmods
    names   = modName `map` mods


    wms = foldl f [] scmods 
        where
        f ws ms = ws ++ zipWith mk ms insouts
            where
            insouts     = computeInsOuts otherExps ms 
            otherExps m = maybe emptyRel expRel $ lookup m ws

    mk mod p = (modName mod, mkWM p)
            
    reportErrs  = filter (not . null . snd) . zip names
   
    inscpOf = inscpRel . fromJust . flip lookup wms
    expsOf  = fmap expRel . flip lookup wms 
    errs    = (\m -> chkModule expsOf (inscpOf (modName m)) m) `map` mods
