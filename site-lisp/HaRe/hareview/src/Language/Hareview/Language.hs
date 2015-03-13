{-# LANGUAGE ExistentialQuantification , DeriveDataTypeable #-}


module Language.Hareview.Language where

import Data.Generics (Typeable)
import Data.Tree (Tree(..))

-- |datatype for one language. Some parsers support source locations
-- which enables us to connect locations in text area with locations
-- in a tree. Selector function @srcLoc@ supports extracting source
-- locations from a subtree (@srcLoc@ will be mapped over the whole
-- tree). @srcLoc@ returns @Nothing@ if current tree does not specify
-- any src loc. Function @adjustSrcLoc@ offers the ability to adjust
-- src locs in abstract data type to our zero point (line 1, row 0)
data Language = forall a s . Language
  { name :: String -- ^ language name
  , syntax :: String -- ^ syntax highlighter name
  , exts :: [String] -- ^ file extentions
  , parse :: String -> Either Error a -- ^ parse function
  , toTree :: a -> Tree String -- to tree
  , srcLoc :: Maybe (Tree String -> [SrcLocation])
    -- ^ selector function for source locations (if supported)
  , adjustSrcLoc :: Maybe (s -> s)
    -- ^ adjust src locs in abstract syntax to
  } deriving Typeable

instance Eq Language where
  l1 == l2 = name l1 == name l2


-- |datatype to specify parse errors
data Error
  = Err -- ^ no error information
  | ErrMessage String -- ^ simple error message
  | ErrLocation SrcLocation String -- ^ error message and src loc

-- |specifies a source location in text area,
-- zero point: line 1, row 0
data SrcLocation = SrcLocation
  { line :: Int
  , row :: Int
  } 
