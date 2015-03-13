module LiftToToplevel.Where1 where

import Data.Tree.DUAL.Internal
import Data.Semigroup
import           Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NEL

unpack = undefined

foldDUALNE :: (Semigroup d, Monoid d)
           => (d -> l -> r) -- ^ Process a leaf datum along with the
                            --   accumulation of @d@ values along the
                            --   path from the root
           -> r             -- ^ Replace @LeafU@ nodes
           -> (NonEmpty r -> r)  -- ^ Combine results at a branch node
           -> (d -> r -> r)      -- ^ Process an internal d node
           -> (a -> r -> r)      -- ^ Process an internal datum
           -> DUALTreeNE d u a l -> r
foldDUALNE  = foldDUALNE' (Option Nothing)
  where
    foldDUALNE' dacc lf _   _   _    _   (Leaf _ l)  = lf (option mempty id dacc) l
    foldDUALNE' _    _  lfU _   _    _   (LeafU _)   = lfU
    foldDUALNE' dacc lf lfU con down ann (Concat ts)
      = con (NEL.map (foldDUALNE' dacc lf lfU con down ann . snd . unpack) ts)
    foldDUALNE' dacc lf lfU con down ann (Act d t)
      = down d (foldDUALNE' (dacc <> (Option (Just d))) lf lfU con down ann . snd . unpack $ t)
    foldDUALNE' dacc lf lfU con down ann (Annot a t)
      = ann a (foldDUALNE' dacc lf lfU con down ann . snd . unpack $ t)
