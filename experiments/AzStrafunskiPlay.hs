{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}

import           TestUtils

import qualified Data.Generics         as SYB
import qualified GHC.SYB.Utils         as SYB

import qualified Bag        as GHC
import qualified FastString as GHC
import qualified GHC        as GHC
import qualified GhcMonad   as GHC
import qualified Name       as GHC
import qualified NameSet    as GHC
import qualified OccName    as GHC
import qualified Outputable as GHC
import qualified RdrName    as GHC
import qualified SrcLoc     as GHC
import qualified Module     as GHC
import qualified UniqSet    as GHC

import Control.Monad.State
import Data.Maybe
import Language.Haskell.Refact.Utils
-- import Language.Haskell.Refact.Utils.GhcUtils
import Language.Haskell.Refact.Utils.LocUtils
import Language.Haskell.Refact.Utils.Monad
import Language.Haskell.Refact.Utils.MonadFunctions
import Language.Haskell.Refact.Utils.TokenUtils
import Language.Haskell.Refact.Utils.TokenUtilsTypes
import Language.Haskell.Refact.Utils.TypeSyn
import Language.Haskell.Refact.Utils.TypeUtils


import Data.List

import Data.Generics.Strafunski.StrategyLib.StrategyLib

-- ---------------------------------------------------------------------

main :: IO ()
main = pp


pp :: IO ()
pp = do
  -- (t, _toks) <- parsedFileDeclareSGhc
  (t, _toks) <- parsedFileLiftWhereIn1Ghc
  let renamed = fromJust $ GHC.tm_renamed_source t
  putStrLn $ "GHC AST:" ++ (SYB.showData SYB.Renamer 0 renamed)
  -- r <- traverseTU2 renamed
  let rl = tu2l renamed
  let rm = tu2m renamed
  let re = tu2e renamed
  -- ri <- tu2i renamed
  -- putStrLn $ "(rm)=" ++ (show (rm))
  -- putStrLn $ "(rm,re,rl)=" ++ (show (rm,re,rl))
  putStrLn $ "(rm,re)=" ++ (show (rm,re))
  -- putStrLn $ "(rm,ri)=" ++ (show (rm,ri))

-- ---------------------------------------------------------------------

tu2i :: (SYB.Data t) => t -> IO [String]
tu2i = traverseTU2

tu2m :: (SYB.Data t) => t -> Maybe [String]
tu2m = traverseTU2

tu2l :: (SYB.Data t) => t -> [] [String]
tu2l = traverseTU2

tu2e :: (SYB.Data t) => t -> Either String [String]
tu2e = traverseTU2

traverseTU2 :: (SYB.Data t, MonadPlus m) => t -> m [String]
traverseTU2 t = do
   -- applyTU (full_tdTUGhc (failTU
   -- applyTU (full_tdTUGhc ((constTU [])
   -- applyTU (stop_tdTUGhc ((constTU ["start"])
   -- applyTU (stop_tdTUGhc (failTU
   applyTU (stop_tdTUGhc (failTU
                `adhocTU` lit
                -- `adhocTU` expr
                -- `adhocTU` mg
   -- applyTU (full_tdTUGhc (failTU `adhocTU` ff
   -- applyTU (full_tdTUGhc (gg `adhocTU` ff
                                      )) t


lit :: (MonadPlus m) => GHC.HsLit -> m [String]
lit (GHC.HsChar n) = return (["lit",[n]])
-- lit _ = return ["foo"]
-- lit _ = return mzero

expr :: (MonadPlus m) => GHC.HsExpr GHC.Name -> m [String]
expr (GHC.HsVar n) = return (["var",GHC.showPpr n])
expr _ = return []

mg :: (MonadPlus m) => GHC.MatchGroup GHC.Name -> m [String]
-- mg (GHC.MatchGroup _ _) = return ["mg"]
-- mg (GHC.MatchGroup _ _) = return mzero
mg (GHC.MatchGroup _ _) = do
  -- s <- mzero :: (MonadPlus m) => m [String]
  -- return [show s]
  return ["show s"]
-- mg _ = return ["nmg"]

-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- | Top-down type-unifying traversal that is cut of below nodes
--   where the argument strategy succeeds.
stop_tdTUGhc :: (MonadPlus m, Monoid a) => TU a m -> TU a m
-- stop_tdTUGhc s = ifTU checkItemRenamer' (const s) (s `choiceTU` (allTUGhc' (stop_tdTUGhc s)))
-- stop_tdTUGhc s = ifTU checkItemRenamer' (const failTU) (s `choiceTU` (allTUGhc' (stop_tdTUGhc s)))
stop_tdTUGhc s = (s `choiceTU` (allTUGhc' (stop_tdTUGhc s)))

{-
-- | Top-down type-unifying traversal that is cut of below nodes
--   where the argument strategy succeeds.
stop_tdTU 	:: (MonadPlus m, Monoid a) => TU a m -> TU a m
stop_tdTU s	=  s `choiceTU` (allTU' (stop_tdTU s))

-}

-- | Full type-unifying traversal in top-down order.
full_tdTUGhc 	:: (MonadPlus m, Monoid a) => TU a m -> TU a m
full_tdTUGhc s	=  op2TU mappend s (allTUGhc' (full_tdTUGhc s))

allTUGhc :: (MonadPlus m) => (a -> a -> a) -> a -> TU a m -> TU a m
allTUGhc op2 u s  = ifTU checkItemRenamer' (const $ constTU u) (allTU op2 u s)

{- This one works, but we cannot use MkTU

allTUGhc :: (Monad m, Monoid a) => (a -> a -> a) -> a -> TU a m -> TU a m
allTUGhc op2 u s = MkTU (\x -> case (checkItemRenamer x) of
                                  True -> do return (u) -- `op2` s)
                                  False -> fold (gmapQ (applyTU s) x)
                          )
  where
    fold l = foldM op2' u l
    op2' x c = c >>= \y -> return (x `op2` y)


-- Original -----
allTU 		:: Monad m => (a -> a -> a) -> a -> TU a m -> TU a m
allTU op2 u s   =  MkTU (\x -> fold (gmapQ (applyTU s) x))
  where
    fold l = foldM op2' u l
    op2' x c = c >>= \y -> return (x `op2` y)


class Typeable a => Data a where
  ...
  gmapQ :: (forall d. Data d => d -> u) -> a -> [u]
  ...

-}

-- MatchGroup [LMatch id] PostTcType
-- gmapQ f (GHC.MatchGroup matches ptt) = [f matches]

{-
-- gmapQ :: (forall d. SYB.Data d => d -> u) -> a -> [u]
instance SYB.Data GHC.NameSet where
  gmapQ f (x::GHC.NameSet)    = []

instance SYB.Data GHC.PostTcType where
  gmapQ f (x::GHC.PostTcType) = []

instance SYB.Data GHC.Fixity where
  gmapQ f (x::GHC.Fixity)     = []
-}


allTUGhc' :: (MonadPlus m, Monoid a) => TU a m -> TU a m
allTUGhc' = allTUGhc mappend mempty

{-

-- | If 'c' succeeds, pass its value to the then-clause 't',
--   otherwise revert to the else-clause 'e'.
ifS       :: StrategyPlus s m => TU u m -> (u -> s m) -> s m -> s m
ifS c t e =  ((c `passTU` (constTU . Just)) `choiceTU` constTU Nothing)
             `passS`
             maybe e t

-- | If 'c' succeeds, pass its value to the then-clause 't',
--   otherwise revert to the else-clause 'e'.
ifTU      :: MonadPlus m => TU u m -> (u -> TU u' m) -> TU u' m -> TU u' m
ifTU      =  ifS

choiceTU 	:: MonadPlus m => TU a m -> TU a m -> TU a m
choiceTU f g	=  MkTU ((unTU f) `mchoice` (unTU g))

newtype Monad m =>
        TU a m =
                 MkTU (forall x. Data x => x -> m a)

unTU (MkTU f)	 = f

paraTU 		:: Monad m => (forall t. t -> m a) -> TU a m
paraTU f	=  MkTU f


-- | Type-unifying failure. Always fails, independent of the incoming
--   term. Uses 'MonadPlus' to model partiality.
failTU          :: MonadPlus m => TU a m
failTU          =  paraTU (const mzero)

applyTU 	:: (Monad m, Data x) => TU a m -> x -> m a
applyTU         =  unTU

-- | Parallel combination of two type-unifying strategies with a binary
--   combinator. In other words, the values resulting from applying the
--   type-unifying strategies are combined to a final value by applying
--   the combinator 'o'.

op2TU :: Monad m => (a -> b -> c) -> TU a m -> TU b m -> TU c m
op2TU o s s' =  s  `passTU` \a ->
                s' `passTU` \b ->
                constTU (o a b)

passTU 		:: Monad m => TU a m -> (a -> TU b m) -> TU b m
passTU f g	=  MkTU ((unTU f) `mlet` (\y -> unTU (g y)))

-- | Sequential composition with value passing; a kind of monadic let.
mlet 		:: Monad m => (a -> m b) -> (b -> a -> m c) -> a -> m c
f `mlet` g    	=  \x -> f x >>= \y -> g y x

-- | Choice combinator for monadic functions
mchoice 	:: MonadPlus m => (a -> m b) -> (a -> m b) -> a -> m b
f `mchoice` g 	=  \x -> (f x) `mplus` (g x)

adhocTU :: (Monad m, Data t) => TU a m -> (t -> m a) -> TU a m
adhocTU s f = MkTU (unTU s `extQ` f)

-- | Extend a generic query by a type-specific case
extQ :: ( Typeable a
        , Typeable b
        )
     => (a -> q)  -- existing query, starting from mkQ, extended via extQ
     -> (b -> q)  -- the new part to be added on
     -> a
     -> q
extQ f g a = maybe (f a) g (cast a)

-- maybe :: b -> (a -> b) -> Maybe a -> b
--   takes default, fn to apply if Just

-- | Make a generic query;
--   start from a type-specific case;
--   return a constant otherwise
--
mkQ :: ( Typeable a
       , Typeable b
       )
    => r
    -> (b -> r)
    -> a
    -> r
(r `mkQ` br) a = case cast a of
                        Just b  -> br b
                        Nothing -> r

-- Type-safe cast
-- The type-safe cast operation 
cast :: (Typeable a, Typeable b) => a -> Maybe b

-}

checkItemStage' :: forall m. (MonadPlus m) => SYB.Stage -> TU () m
checkItemStage' stage = failTU `adhocTU` postTcType `adhocTU` fixity `adhocTU` nameSet
  where nameSet    = (const (guard $ stage `elem` [SYB.Parser,SYB.TypeChecker])) :: GHC.NameSet    -> m ()
        postTcType = (const (guard $ stage < SYB.TypeChecker                  )) :: GHC.PostTcType -> m ()
        fixity     = (const (guard $ stage < SYB.Renamer                      )) :: GHC.Fixity     -> m ()



checkItemRenamer' :: (MonadPlus m) => TU () m
checkItemRenamer' = checkItemStage' SYB.Renamer
-- checkItemRenamer' = failTU

{-
-- fixity :: (MonadPlus m) => SYB.Stage -> a -> GHC.Fixity -> m ()
fixity :: (MonadPlus m) => SYB.Stage -> a -> GHC.Fixity -> m a
fixity stage u _x = do
  guard (stage < SYB.Renamer)
  return u

postTcType :: (MonadPlus m) => SYB.Stage -> a -> GHC.PostTcType -> m a
postTcType stage u _x = do
  guard $ stage < SYB.TypeChecker
  return u

nameSet :: (MonadPlus m) => SYB.Stage -> a -> GHC.NameSet -> m a
nameSet stage u _x = do
  guard $ stage `elem` [SYB.Parser,SYB.TypeChecker]
  return u
-}

-- ---------------------------------------------------------------------

parsedFileDeclareSGhc :: IO (ParseResult,[PosToken])
parsedFileDeclareSGhc = parsedFileGhc "./test/testdata/FreeAndDeclared/DeclareS.hs"


parsedFileLiftWhereIn1Ghc :: IO (ParseResult,[PosToken])
parsedFileLiftWhereIn1Ghc = parsedFileGhc "./test/testdata/LiftToToplevel/WhereIn1.hs"
