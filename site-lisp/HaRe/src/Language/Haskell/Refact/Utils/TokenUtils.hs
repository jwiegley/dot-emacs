{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- |
--
-- This module contains an API to manage a token stream.
--
-- This API is used internally by MonadFunctions and the other utility
-- modules, it should probably never be used directly in a refactoring.

module Language.Haskell.Refact.Utils.TokenUtils (
       -- * Operations at 'TokenCache' level
         putDeclToksInCache
       , syncAstToLatestCache

       -- * Operations at 'Tree' 'Entry' level
       , addDeclToksAfterSrcSpan
       , syncAST

       -- * Utility
       , posToSrcSpan
       , posToSrcSpanTok

       -- * Internal, for testing
       , nonCommentSpan
       , showSrcSpan
       , showSrcSpanF
       , ghcSpanStartEnd
       , stripForestLineFromGhc
       , ghcSrcSpanToForestSpan
       , deleteGapsToks
       ) where

-- import qualified FastString    as GHC
import qualified GHC           as GHC

import qualified Data.Generics as SYB
import qualified GHC.SYB.Utils as SYB

import Language.Haskell.Refact.Utils.GhcUtils
import Language.Haskell.Refact.Utils.LocUtils
import Language.Haskell.Refact.Utils.TypeSyn

import Language.Haskell.TokenUtils.GHC.Layout
import Language.Haskell.TokenUtils.TokenUtils
import Language.Haskell.TokenUtils.Types
import Language.Haskell.TokenUtils.Utils

import Data.Tree
import qualified Data.Map as Map

-- import Debug.Trace
-- debug = flip trace

-- ---------------------------------------------------------------------

ghcSrcSpanToForestSpan :: GHC.SrcSpan -> ForestSpan
ghcSrcSpanToForestSpan sspan = ((ghcLineToForestLine startRow,startCol),(ghcLineToForestLine endRow,endCol))
  where
    (startRow,startCol) = getGhcLoc sspan
    (endRow,endCol)     = getGhcLocEnd sspan

-- ---------------------------------------------------------------------

putDeclToksInCache :: (SYB.Data t) =>
    TokenCache PosToken -> GHC.SrcSpan -> [PosToken] -> GHC.Located t
 -> (TokenCache PosToken,GHC.SrcSpan,GHC.Located t)
putDeclToksInCache tk sspan toks t = (tk'',ss2gs newSpan,t')
  where
   (tk'',newSpan) = putToksInCache tk (gs2ss sspan) toks
   t' = syncAST t (ss2f newSpan)

-- ---------------------------------------------------------------------

-- |Assuming most recent operation has stashed the old tokens, sync
-- the given AST to the most recent stash entry
syncAstToLatestCache :: (SYB.Data t) => TokenCache PosToken -> GHC.Located t -> GHC.Located t
syncAstToLatestCache tk t = t'
  where
    mainForest = (tkCache tk) Map.! mainTid
    (Node (Entry fspan _ _) _) = (tkCache tk) Map.! (tkLastTreeId tk)
    pos = forestSpanToGhcPos fspan
    sspan = posToSrcSpan mainForest pos
    t' = syncAST t (gs2f sspan)

-- ---------------------------------------------------------------------

-- | Process the leaf nodes of a tree to remove all deleted spans
deleteGapsToks :: [Entry PosToken] -> [PosToken]
deleteGapsToks toks = goDeleteGapsToks (0,0) toks

goDeleteGapsToks :: SimpPos -> [Entry PosToken] -> [PosToken]
goDeleteGapsToks      _ []                    = []
goDeleteGapsToks offset [Entry _ _ t]         = map (increaseSrcSpan offset) t
goDeleteGapsToks      _ [Deleted _ _ _]       = []
goDeleteGapsToks offset (Deleted _ _ _:ts)    = goDeleteGapsToks offset ts
goDeleteGapsToks offset [Entry _ _ t,Deleted _ _ _] = map (increaseSrcSpan offset) t
goDeleteGapsToks offset (Entry _ _ t1:e@(Entry _ _ _):ts) = (map (increaseSrcSpan offset) t1) ++goDeleteGapsToks offset (e:ts)
goDeleteGapsToks (fr,fc) (Entry ss _lay1 t1:Deleted _ _ eg:t2:ts)
  = t1' ++ goDeleteGapsToks offset' (t2:ts)
  where
    -- TODO: use actual first and last toks, may be comments
    -- TODO: what about deletion within a line?

    (deltaR,_deltaC) = eg
    (_,(sr,_sc)) = forestSpanToSimpPos ss
    ((dr,_dc),_) = forestSpanToSimpPos $ forestSpanFromEntry t2
    offset' = (fr + (sr - dr) + deltaR, fc)

    t1' = map (increaseSrcSpan (fr,fc)) t1

-- ---------------------------------------------------------------------

stripForestLineFromGhc :: GHC.SrcSpan -> GHC.SrcSpan
stripForestLineFromGhc l = l'
  where
    ((ForestLine _ _ _ ls,_),(_,_)) = ghcSrcSpanToForestSpan l
    l' = insertForestLineInSrcSpan (ForestLine False 0 0 ls) l

-- ---------------------------------------------------------------------

-- |Add new tokens belonging to an AST fragment after a given SrcSpan,
-- and re-sync the AST fragment to match the new location
addDeclToksAfterSrcSpan :: (SYB.Data t) =>
     Tree (Entry PosToken)  -- ^TokenTree to be modified
  -> GHC.SrcSpan -- ^Preceding location for new tokens
  -> Positioning
  -> [PosToken] -- ^New tokens to be added
  -> GHC.Located t  -- ^Declaration the tokens belong to, to be synced
  -> (Tree (Entry PosToken), GHC.SrcSpan,GHC.Located t) -- ^ updated TokenTree ,SrcSpan location for
  -- -> (Tree (Entry PosToken), GHC.SrcSpan,t) -- ^ updated TokenTree ,SrcSpan location for
                               -- the new tokens in the TokenTree, and
                               -- updated AST element
addDeclToksAfterSrcSpan forest oldSpan pos toks t = (forest',(ss2gs newSpan),t')
  where
    (forest',newSpan) = addToksAfterSrcSpan forest (gs2ss oldSpan) pos toks
    t' = syncAST t (ss2f newSpan)

-- ---------------------------------------------------------------------

-- |Convert a simple (start,end) position to a SrcSpan belonging to
-- the file in the tree
posToSrcSpan :: Tree (Entry PosToken) -> (SimpPos,SimpPos) -> GHC.SrcSpan
posToSrcSpan forest ((rs,cs),(re,ce)) = sspan
  where
    (GHC.L l _,_) = ghead "posToSrcSpan"  $ retrieveTokensInterim forest -- ++AZ++ Ouch, performance??
    sspan =  case l of
      GHC.RealSrcSpan ss ->
        let
          locStart = GHC.mkSrcLoc (GHC.srcSpanFile ss) rs cs
          locEnd   = GHC.mkSrcLoc (GHC.srcSpanFile ss) re ce
        in
          GHC.mkSrcSpan locStart locEnd
      _ -> error "posToSrcSpan: invalid SrcSpan in first tok"

-- ---------------------------------------------------------------------

-- |Convert a simple (start,end) position to a SrcSpan belonging to
-- the file in the given token
posToSrcSpanTok :: PosToken -> (SimpPos,SimpPos) -> GHC.SrcSpan
posToSrcSpanTok tok ((rs,cs),(re,ce)) = sspan
  where
    (GHC.L l _,_) = tok
    sspan =  case l of
      GHC.RealSrcSpan ss ->
        let
          locStart = GHC.mkSrcLoc (GHC.srcSpanFile ss) rs cs
          locEnd   = GHC.mkSrcLoc (GHC.srcSpanFile ss) re ce
        in
          GHC.mkSrcSpan locStart locEnd
      _ -> error "posToSrcSpan: invalid SrcSpan in first tok"

-- ---------------------------------------------------------------------
{-
-- |Get the start and end position of a SrcSpan
-- spanStartEnd :: GHC.SrcSpan -> (SimpPos,SimpPos)
-- spanStartEnd sspan = (getGhcLoc sspan,getGhcLocEnd sspan)
spanStartEnd :: GHC.SrcSpan -> ForestSpan
spanStartEnd sspan = ((ghcLineToForestLine sr,sc),(ghcLineToForestLine er,ec))
  where
    ((sr,sc),(er,ec)) = (getGhcLoc sspan,getGhcLocEnd sspan)
-}
-- ---------------------------------------------------------------------

ghcSpanStartEnd :: GHC.SrcSpan -> ((Int, Int), (Int, Int))
ghcSpanStartEnd sspan = (getGhcLoc sspan,getGhcLocEnd sspan)

-- ---------------------------------------------------------------------

-- |Synchronise a located AST fragment to use a newly created SrcSpan
-- in the token tree.
-- TODO: Should this indent the tokens as well?
syncAST :: (SYB.Data t)
  => GHC.Located t -- ^The AST (or fragment)
  -> ForestSpan   -- ^The SrcSpan created in the Tree (Entry PosToken)
  -> (GHC.Located t) -- ^Updated AST and tokens
syncAST ast@(GHC.L l _t) fspan = GHC.L sspan xx
  where
    sspan = f2gs fspan
    (( sr, sc),( _er, _ec)) = ghcSpanStartEnd l
    ((nsr,nsc),(_ner,_nec)) = ghcSpanStartEnd sspan

    rowOffset = nsr - sr
    colOffset = nsc - sc

    -- TODO: take cognizance of the ForestLines encoded in srcspans
    -- when calculating the offsets etc
    syncSpan s  = addOffsetToSrcSpan (rowOffset,colOffset) s

    (GHC.L _s xx) = everywhereStaged SYB.Renamer (
              SYB.mkT hsbindlr
              `SYB.extT` sig
              `SYB.extT` ty
              `SYB.extT` name
              `SYB.extT` lhsexpr
              `SYB.extT` lpat
              `SYB.extT` limportdecl
              `SYB.extT` lmatch
              ) ast

    hsbindlr (GHC.L s b)    = (GHC.L (syncSpan s) b) :: GHC.Located (GHC.HsBindLR GHC.Name GHC.Name)
    sig (GHC.L s n)         = (GHC.L (syncSpan s) n) :: GHC.LSig GHC.Name
    ty (GHC.L s typ)        = (GHC.L (syncSpan s) typ) :: (GHC.LHsType GHC.Name)
    name (GHC.L s n)        = (GHC.L (syncSpan s) n) :: GHC.Located GHC.Name
    lhsexpr (GHC.L s e)     = (GHC.L (syncSpan s) e) :: GHC.LHsExpr GHC.Name
    lpat (GHC.L s p)        = (GHC.L (syncSpan s) p) :: GHC.LPat GHC.Name
    limportdecl (GHC.L s n) = (GHC.L (syncSpan s) n) :: GHC.LImportDecl GHC.Name
    lmatch (GHC.L s m)      = (GHC.L (syncSpan s) m) :: GHC.LMatch GHC.Name

-- ---------------------------------------------------------------------

addOffsetToSrcSpan :: (Int,Int) -> GHC.SrcSpan -> GHC.SrcSpan
addOffsetToSrcSpan (lineOffset,colOffset) sspan = sspan'
  where
   sspan' =  case sspan of
     GHC.RealSrcSpan ss ->
       let
         locStart = GHC.mkSrcLoc (GHC.srcSpanFile ss) (lineOffset + GHC.srcSpanStartLine ss) (colOffset + GHC.srcSpanStartCol ss) 
         locEnd   = GHC.mkSrcLoc (GHC.srcSpanFile ss) (lineOffset + GHC.srcSpanEndLine ss)  (colOffset + GHC.srcSpanEndCol ss) 
       in
         GHC.mkSrcSpan locStart locEnd
     _ -> sspan

-- ---------------------------------------------------------------------

-- EOF
