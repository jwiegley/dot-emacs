{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Language.Hareview.Languages.Haskell where

-- container
import Data.Tree (Tree(Node,rootLabel))

-- local imports
import Language.Hareview.Language

import Language.Haskell.Exts 
import Language.Haskell.Exts.Parser
import Language.Haskell.Exts.Syntax

import Language.Hareview.DataTree (data2tree)

haskellexts = Language 
  "Haskell" 
  "Haskell" 
  [".hs",".lhs"] 
  parHaskell
  (data2tree::Module->Tree String)
  (Just toSrcLoc)
  Nothing
    
parHaskell :: String -> Either Error Module
parHaskell s =
  case parseFileContents s of
    ParseOk t   -> Right t
    ParseFailed (SrcLoc _ l c) m -> 
      Left $ ErrLocation (SrcLocation l c) m


toSrcLoc :: Tree String -> [SrcLocation]
toSrcLoc (Node "SrcLoc" cs) = 
  [SrcLocation (read (to 1)::Int) (read (to 2):: Int)] 
  where to = rootLabel . (cs !!)
toSrcLoc _        = [] 
