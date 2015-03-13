{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeSynonymInstances   #-}
{-# LANGUAGE OverlappingInstances   #-}

module Term2tree (data2tree) where

import Generics.MultiRec.Base
import Generics.MultiRec.HFunctor
import Generics.MultiRec.Constructor
import Generics.MultiRec.TH
import qualified Data.Tree as DT
import Data.Traversable
-- import ListOf

data Tree = Node String [Tree] deriving (Show)

data2tree :: forall phi ix. (Fam phi, Data2Tree phi (PF phi)) => phi ix -> ix -> DT.Tree String
data2tree p = tree2tree . data2tree' p

tree2tree :: Tree -> DT.Tree String
tree2tree (Node s ts) = DT.Node s (map tree2tree ts)

data2tree' :: forall phi ix. (Fam phi, Data2Tree phi (PF phi)) => phi ix -> ix -> Tree
data2tree' p x = head $ hData2Tree p (\p' (I0 x') -> [data2tree' p' x']) (from p x)

class Data2Tree (phi :: * -> *) (f :: (* -> *) -> * -> *) where
  hData2Tree :: phi ix -> (forall ix. phi ix -> r ix -> [Tree]) -> f r ix -> [Tree]

instance (Constructor c, Data2Tree phi f) => Data2Tree phi (C c f) where
  hData2Tree p r cx@(C f) = [Node (conName cx) (hData2Tree p r f)]

instance (Data2Tree phi f, Data2Tree phi g) => Data2Tree phi (f :+: g) where
  hData2Tree p r (L f) = hData2Tree p r f
  hData2Tree p r (R f) = hData2Tree p r f

-- instance (Data2Tree phi f) => Data2Tree phi (ListOf f) where
-- --  hData2Tree p r (ListOf frxs) = [Node "ListOf" (hData2Tree p r (head frxs))]
--   hData2Tree p r (ListOf frxs) = [Node "ListOf" (concatMap (hData2Tree p r) frxs)]


instance (Show x) => Data2Tree phi (K x) where
  hData2Tree _ _ (K x) = [Node (show x) []]
  
instance Data2Tree phi (K String) where
  hData2Tree _ _ (K s) = [Node s []]

instance Data2Tree phi U where
  hData2Tree _ _ _ = []

instance (Data2Tree phi f, Data2Tree phi g) => Data2Tree phi (f :*: g) where
  hData2Tree p r (f :*: g) = hData2Tree p r f ++ hData2Tree p r g

instance (El phi ix) => Data2Tree phi (I ix) where
  hData2Tree p r (I x) = r proof x

instance (Data2Tree phi f) => Data2Tree phi (f :>: ix) where
  hData2Tree p r (Tag f) = hData2Tree p r f


