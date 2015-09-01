{-# LANGUAGE ScopedTypeVariables #-}
module Language.Haskell.Refact.HaRe
 (
 -- * Data Structures
   RefactSettings(..)
 , VerboseLevel (..)
 , defaultSettings
 , SimpPos

 -- * Refactorings
 -- |Note: the 'Cradle' in the type signatures is the one from ghc-mod
 , ifToCase
 , duplicateDef
 , liftToTopLevel
 , liftOneLevel
 , demote
 , rename
 , swapArgs
 )
where

import Language.Haskell.Refact.Refactoring.Case
import Language.Haskell.Refact.Refactoring.DupDef
import Language.Haskell.Refact.Refactoring.MoveDef
import Language.Haskell.Refact.Refactoring.Renaming
import Language.Haskell.Refact.Refactoring.SwapArgs
import Language.Haskell.Refact.Utils.Monad
import Language.Haskell.TokenUtils.Types

