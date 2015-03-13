{-# LANGUAGE ScopedTypeVariables #-}
















import qualified Data.Generics as SYB
import qualified GHC.SYB.Utils as SYB

import GHC
import NameSet
import Control.Monad

import Data.Data

import Data.Generics.Strafunski.StrategyLib.StrategyLib

-- Question: how to replace MkTU with paraTU?
{-
allTUGhc :: (Monad m, Monoid a) => (a -> a -> a) -> a -> TU a m -> TU a m
allTUGhc op2 u s  =  paraTU (\x -> case (checkItemRenamer x) of
                                  True -> do return (u) -- `op2` s)
                                  False ->  fold (gmapQ (applyTU s) x)
                          )
  where
    fold l = foldM op2' u l
    op2' x c = c >>= \y -> return (x `op2` y)
-}
allTUGhc :: (MonadPlus m) => (a -> a -> a) -> a -> TU a m -> TU a m
allTUGhc op2 u s  = ifTU checkItemRenamer' (const $ constTU u) (allTU op2 u s)







checkItemStage' :: forall m. (MonadPlus m) => SYB.Stage -> TU () m
checkItemStage' stage = failTU `adhocTU` postTcType `adhocTU` fixity `adhocTU` nameSet
  where nameSet = const (guard $ stage `elem` [SYB.Parser,SYB.TypeChecker]) :: NameSet -> m ()
        postTcType = const (guard $ stage<SYB.TypeChecker) :: GHC.PostTcType -> m ()
        fixity = const (guard $ stage<SYB.Renamer) :: GHC.Fixity -> m ()

checkItemRenamer' :: (MonadPlus m) => TU () m
checkItemRenamer' = checkItemStage' SYB.Renamer








-- | Checks whether the current item is undesirable for analysis in the current
-- AST Stage.
checkItemStage :: Typeable a => SYB.Stage -> a -> Bool
checkItemStage stage x = (const False `SYB.extQ` postTcType `SYB.extQ` fixity `SYB.extQ` nameSet) x
  where nameSet = const (stage `elem` [SYB.Parser,SYB.TypeChecker]) :: NameSet -> Bool
        postTcType = const (stage<SYB.TypeChecker) :: GHC.PostTcType -> Bool
        fixity = const (stage<SYB.Renamer) :: GHC.Fixity -> Bool

checkItemRenamer :: Typeable a => a -> Bool
checkItemRenamer x = checkItemStage SYB.Renamer x
