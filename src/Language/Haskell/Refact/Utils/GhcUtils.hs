{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-|

This module contains routines used to perform generic traversals of
the GHC AST, avoiding the traps resulting from certain fields being
populated with values defined to trigger an error if ever evaluated.

This is a useful feature for tracking down bugs in GHC, but makes use
of the GHC library problematic.

-}

module Language.Haskell.Refact.Utils.GhcUtils (
    -- * SYB versions
      everythingButStaged
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

    -- ** SYB Utility
    , checkItemRenamer

    -- * Strafunski StrategyLib versions
    , full_tdTUGhc
    , stop_tdTUGhc
    , stop_tdTPGhc
    , allTUGhc'
    , once_tdTPGhc
    , once_buTPGhc
    , oneTPGhc
    , allTUGhc

    -- ** Strafunski utility
    , checkItemStage'
    , checkItemRenamer'

    -- * Scrap Your Zipper versions
    , zeverywhereStaged
    , zopenStaged
    , zsomewhereStaged
    , transZ
    , transZM
    , zopenStaged'
    , ztransformStagedM
    -- ** SYZ utilities
    , checkZipperStaged
    , upUntil
    , findAbove
    ) where

import qualified Data.Generics as SYB
import qualified GHC.SYB.Utils as SYB

import Control.Monad
import Data.Data
import Data.Maybe

import qualified GHC     as GHC
import qualified NameSet as GHC

import Data.Generics.Strafunski.StrategyLib.StrategyLib

import qualified Data.Generics.Zipper as Z

-- TODO: pass this routine back to syb-utils (when it works properly)
-- Question: how to handle partial results in the otherwise step?
everythingButStaged :: SYB.Stage -> (r -> r -> r) -> r -> SYB.GenericQ (r,Bool) -> SYB.GenericQ r
everythingButStaged stage k z f x
  | checkItemStage stage x = z
  | stop == True = v
  | otherwise = foldl k v (gmapQ (everythingButStaged stage k z f) x)
  where (v, stop) = f x


{-
-- | Look up a subterm by means of a maybe-typed filter
something :: GenericQ (Maybe u) -> GenericQ (Maybe u)

-- "something" can be defined in terms of "everything"
-- when a suitable "choice" operator is used for reduction
--
something = everything orElse
-}

-- | Look up a subterm by means of a maybe-typed filter
somethingStaged :: SYB.Stage -> (Maybe u) -> SYB.GenericQ (Maybe u) -> SYB.GenericQ (Maybe u)

-- "something" can be defined in terms of "everything"
-- when a suitable "choice" operator is used for reduction
--
somethingStaged stage z = everythingStaged stage SYB.orElse z

-- ---------------------------------------------------------------------

{-
-- | Apply a monadic transformation at least somewhere
somewhere :: MonadPlus m => GenericM m -> GenericM m

-- We try "f" in top-down manner, but descent into "x" when we fail
-- at the root of the term. The transformation fails if "f" fails
-- everywhere, say succeeds nowhere.
--
somewhere f x = f x `mplus` gmapMp (somewhere f) x
-}

-- | Apply a monadic transformation at least somewhere
somewhereMStaged :: MonadPlus m => SYB.Stage -> SYB.GenericM m -> SYB.GenericM m

-- We try "f" in top-down manner, but descent into "x" when we fail
-- at the root of the term. The transformation fails if "f" fails
-- everywhere, say succeeds nowhere.
--
somewhereMStaged stage f x
  | checkItemStage stage x = mzero
  | otherwise = f x `mplus` gmapMp (somewhereMStaged stage f) x

-- ---------------------------------------------------------------------

-- | Apply a monadic transformation at least somewhere, in bottom up order
somewhereMStagedBu :: MonadPlus m => SYB.Stage -> SYB.GenericM m -> SYB.GenericM m
somewhereMStagedBu stage f x
  | checkItemStage stage x = mzero
  -- was | otherwise = f x `mplus` gmapMp (somewhereMStaged stage f) x
  | otherwise =  gmapMp (somewhereMStagedBu stage f) x `mplus` f x


-- ---------------------------------------------------------------------

-- | Monadic variation on everywhere
everywhereMStaged :: Monad m => SYB.Stage -> SYB.GenericM m -> SYB.GenericM m

-- Bottom-up order is also reflected in order of do-actions
everywhereMStaged stage f x
  | checkItemStage stage x = return x
  | otherwise = do x' <- gmapM (everywhereMStaged stage f) x
                   f x'


-- | Monadic variation on everywhere'
everywhereMStaged' :: Monad m => SYB.Stage -> SYB.GenericM m -> SYB.GenericM m

-- Top-down order is also reflected in order of do-actions
everywhereMStaged' stage f x
  | checkItemStage stage x = return x
  | otherwise = do x' <- f x
                   gmapM (everywhereMStaged' stage f) x'


-- ---------------------------------------------------------------------

-- | Bottom-up transformation
everywhereStaged ::  SYB.Stage -> (forall a. Data a => a -> a) -> forall a. Data a => a -> a
everywhereStaged stage f x
  | checkItemStage stage x = x
  | otherwise = (f . gmapT (everywhereStaged stage f)) x

-- | Top-down version of everywhereStaged
everywhereStaged' ::  SYB.Stage -> (forall a. Data a => a -> a) -> forall a. Data a => a -> a
everywhereStaged' stage f x
  | checkItemStage stage x = x
  | otherwise = (gmapT (everywhereStaged stage f) . f) x

-- ---------------------------------------------------------------------

-- From @frsoares

-- | Checks whether the current item is undesirable for analysis in the current
-- AST Stage.
checkItemStage :: (Typeable a, Data a) => SYB.Stage -> a -> Bool
checkItemStage stage x = (checkItemStage1 stage x)
#if __GLASGOW_HASKELL__ > 704
                      || (checkItemStage2 stage x)
#endif

-- Check the Typeable items
checkItemStage1 :: (Typeable a) => SYB.Stage -> a -> Bool
checkItemStage1 stage x = (const False `SYB.extQ` postTcType `SYB.extQ` fixity `SYB.extQ` nameSet) x
  where nameSet     = const (stage `elem` [SYB.Parser,SYB.TypeChecker]) :: GHC.NameSet       -> Bool
        postTcType  = const (stage < SYB.TypeChecker                  ) :: GHC.PostTcType    -> Bool
        fixity      = const (stage < SYB.Renamer                      ) :: GHC.Fixity        -> Bool

#if __GLASGOW_HASKELL__ > 704
-- | Check the Typeable1 items
checkItemStage2 :: Data a => SYB.Stage -> a -> Bool
checkItemStage2 stage x = (const False `SYB.ext1Q` hsWithBndrs) x
  where
        hsWithBndrs = const (stage < SYB.Renamer) :: GHC.HsWithBndrs a -> Bool
#endif

checkItemRenamer :: (Data a, Typeable a) => a -> Bool
checkItemRenamer x = checkItemStage SYB.Renamer x



-- | Staged variation of SYB.everything
-- The stage must be provided to avoid trying to modify elements which
-- may not be present at all stages of AST processing.
-- Note: Top-down order
everythingStaged :: SYB.Stage -> (r -> r -> r) -> r -> SYB.GenericQ r -> SYB.GenericQ r
everythingStaged stage k z f x
  | checkItemStage stage x = z
  | otherwise = foldl k (f x) (gmapQ (everythingStaged stage k z f) x)


-- ---------------------------------------------------------------------

-- |Perform a query on the immediate subterms only, avoiding holes
onelayerStaged :: SYB.Stage -> r -> SYB.GenericQ r -> SYB.GenericQ [r]
onelayerStaged stage z f t = gmapQ stagedF t
-- onelayerStaged stage z f t = (stagedF t) : gmapQ stagedF t
  where
    stagedF x
      | checkItemStage stage x = z
      | otherwise = f x

-- ---------------------------------------------------------------------

-- | Staged variation of SYB.listify
-- The stage must be provided to avoid trying to modify elements which
-- may not be present at all stages of AST processing.
listifyStaged
  :: (Data a, Typeable a1) => SYB.Stage -> (a1 -> Bool) -> a -> [a1]
listifyStaged stage p = everythingStaged stage (++) [] ([] `SYB.mkQ` (\x -> [ x | p x ]))



-- ---------------------------------------------------------------------

-- Strafunski StrategyLib adaptations

-- ---------------------------------------------------------------------

-- | Full type-unifying traversal in top-down order.
full_tdTUGhc    :: (MonadPlus m, Monoid a) => TU a m -> TU a m
full_tdTUGhc s  =  op2TU mappend s (allTUGhc' (full_tdTUGhc s))

-- ---------------------------------------------------------------------
-- | Top-down type-unifying traversal that is cut of below nodes
--   where the argument strategy succeeds.
stop_tdTUGhc :: (MonadPlus m, Monoid a) => TU a m -> TU a m
stop_tdTUGhc s = (s `choiceTU` (allTUGhc' (stop_tdTUGhc s)))

-- | Top-down type-preserving traversal that is cut of below nodes
--   where the argument strategy succeeds.
stop_tdTPGhc 	:: MonadPlus m => TP m -> TP m
stop_tdTPGhc s	=  s `choiceTP` (allTPGhc (stop_tdTPGhc s))


allTUGhc' :: (MonadPlus m, Monoid a) => TU a m -> TU a m
allTUGhc' = allTUGhc mappend mempty

-- | Top-down type-preserving traversal that performs its argument
--   strategy at most once.
once_tdTPGhc    :: MonadPlus m => TP m -> TP m
once_tdTPGhc s  =  s `choiceTP` (oneTPGhc (once_tdTPGhc s))

-- | Bottom-up type-preserving traversal that performs its argument
--   strategy at most once.
once_buTPGhc    :: MonadPlus m => TP m -> TP m
once_buTPGhc s  =  (oneTPGhc (once_buTPGhc s)) `choiceTP` s

-- Succeed for one child; don't care about the other children
oneTPGhc          :: MonadPlus m => TP m -> TP m
oneTPGhc s         =  ifTP checkItemRenamer' (const failTP) (oneTP s)

-- Succeed for all children
allTPGhc :: MonadPlus m => TP m -> TP m
allTPGhc s = ifTP checkItemRenamer' (const failTP) (oneTP s)

------------------------------------------

-- This section courtesy of @jkoppel (James Koppel)
allTUGhc :: (MonadPlus m) => (a -> a -> a) -> a -> TU a m -> TU a m
allTUGhc op2 u s  = ifTU checkItemRenamer' (const $ constTU u) (allTU op2 u s)


checkItemStage' :: forall m. (MonadPlus m) => SYB.Stage -> TU () m
checkItemStage' stage = failTU `adhocTU` postTcType `adhocTU` fixity `adhocTU` nameSet
  where nameSet    = const (guard $ stage `elem` [SYB.Parser,SYB.TypeChecker]) :: GHC.NameSet -> m ()
        postTcType = const (guard $ stage<SYB.TypeChecker) :: GHC.PostTcType -> m ()
        fixity     = const (guard $ stage<SYB.Renamer) :: GHC.Fixity -> m ()

checkItemRenamer' :: (MonadPlus m) => TU () m
checkItemRenamer' = checkItemStage' SYB.Renamer

-- ---------------------------------------------------------------------

-- Scrap-your-zippers for ghc

-- | Apply a generic transformation everywhere in a bottom-up manner.
zeverywhereStaged :: (Typeable a) => SYB.Stage -> SYB.GenericT -> Z.Zipper a -> Z.Zipper a
zeverywhereStaged stage f z
  | checkZipperStaged stage z = z
  | otherwise = Z.trans f (Z.downT g z)
  where
    g z' = Z.leftT g (zeverywhereStaged stage f z')


-- | Open a zipper to the point where the Geneneric query passes.
-- returns the original zipper if the query does not pass (check this)
zopenStaged :: (Typeable a) => SYB.Stage -> SYB.GenericQ Bool -> Z.Zipper a -> [Z.Zipper a]
zopenStaged stage q z
  | checkZipperStaged stage z = []
  | Z.query q z = [z]
  | otherwise = reverse $ Z.downQ [] g z
  where
    g z' = (zopenStaged stage q z') ++ (Z.leftQ [] g z')

-- | Apply a generic monadic transformation once at the topmost
-- leftmost successful location, avoiding holes in the GHC structures
zsomewhereStaged :: (MonadPlus m) => SYB.Stage -> SYB.GenericM m -> Z.Zipper a -> m (Z.Zipper a)
zsomewhereStaged stage f z
  | checkZipperStaged stage z = return z
  | otherwise = Z.transM f z `mplus` Z.downM mzero (g . Z.leftmost) z
  where
    g z' = Z.transM f z `mplus` Z.rightM mzero (zsomewhereStaged stage f) z'


-- | Transform a zipper opened with a given generic query
transZ :: SYB.Stage -> SYB.GenericQ Bool -> (SYB.Stage -> Z.Zipper a -> Z.Zipper a) -> Z.Zipper a -> Z.Zipper a
transZ stage q t z
  | Z.query q z = t stage z
  | otherwise = z

-- | Monadic transform of a zipper opened with a given generic query
transZM :: Monad m
  => SYB.Stage
  -> SYB.GenericQ Bool
  -> (SYB.Stage -> Z.Zipper a -> m (Z.Zipper a))
  -> Z.Zipper a
  -> m (Z.Zipper a)
transZM stage q t z
  | Z.query q z = t stage z
  | otherwise = return z


checkZipperStaged :: SYB.Stage -> Z.Zipper a -> Bool
checkZipperStaged stage z
  | isJust maybeNameSet    = checkItemStage stage (fromJust maybeNameSet)
  | isJust maybePostTcType = checkItemStage stage (fromJust maybePostTcType)
  | isJust maybeFixity     = checkItemStage stage (fromJust maybeFixity)
  -- was | isJust maybeHsWithBndrs = checkItemStage stage (fromJust maybeHsWithBndrs)
  | otherwise = False
  where
    maybeNameSet ::  Maybe GHC.NameSet
    maybeNameSet = Z.getHole z

    maybePostTcType :: Maybe GHC.PostTcType
    maybePostTcType = Z.getHole z

    maybeFixity :: Maybe GHC.Fixity
    maybeFixity = Z.getHole z

    -- maybeHsWithBndrs :: (Data b) => Maybe (GHC.HsWithBndrs b)
    -- maybeHsWithBndrs = Z.getHole z

-- ---------------------------------------------------------------------

-- | Climb the tree until a predicate holds
upUntil :: SYB.GenericQ Bool -> Z.Zipper a -> Maybe (Z.Zipper a)
upUntil q z
  | Z.query q z = Just z
  | otherwise = Z.upQ Nothing (upUntil q) z

-- ---------------------------------------------------------------------

-- | Up the zipper until a predicate holds, and then return the zipper
-- hole
findAbove :: (Data a) => (a -> Bool) -> Z.Zipper a -> Maybe a
findAbove cond z = do
    zu  <- upUntil (False `SYB.mkQ` cond) z
    res <- (Z.getHole zu)
    return res

-- ---------------------------------------------------------------------

-- | Open a zipper to the point where the Generic query passes,
-- returning the zipper and a value from the specific part of the
-- GenericQ that matched. This allows the components of the query to
-- return a specific transformation routine, to apply to the returned zipper
zopenStaged' :: (Typeable a)
  => SYB.Stage
  -> SYB.GenericQ (Maybe b)
  -> Z.Zipper a
  -> [(Z.Zipper a,b)]
zopenStaged' stage q z
  | checkZipperStaged stage z = []
  | isJust zq = [(z,fromJust zq)]
  | otherwise = reverse $ Z.downQ [] g z
  where
    g z' = (zopenStaged' stage q z') ++ (Z.leftQ [] g z')

    zq = Z.query q z


-- | Open a zipper to the point where the Generic query passes,
-- and apply the transformation returned from the specific part of the
-- GenericQ that matched.
ztransformStagedM :: (Typeable a,Monad m)
  => SYB.Stage
  -> SYB.GenericQ (Maybe (SYB.Stage -> Z.Zipper a -> m (Z.Zipper a)))
  -> Z.Zipper a
  -> m (Z.Zipper a)
ztransformStagedM stage q z = do
    let zs = zopenStaged' stage q z
    z' <- case zs of
           [(zz,t)] -> t stage zz
           _        -> return z
    return z'

