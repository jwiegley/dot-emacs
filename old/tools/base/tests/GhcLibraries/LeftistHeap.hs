-- Dummny LeftistHeap module
module LeftistHeap where

import Sequence
data Heap a

maxElem :: Ord a => Heap a -> a
maxElem = undefined

null :: Ord a => Heap a -> Bool
null = undefined

delete :: Ord a => a -> Heap a -> Heap a
delete = undefined

insert :: Ord a => a -> Heap a -> Heap a
insert = undefined

empty :: Ord a => Heap a
empty = undefined

deleteMax :: Ord a => Heap a -> Heap a
deleteMax = undefined

toSeq :: (Ord a, Sequence seq) => Heap a -> seq a
toSeq = undefined

filter :: Ord a => (a -> Bool) -> Heap a -> Heap a
filter = undefined
