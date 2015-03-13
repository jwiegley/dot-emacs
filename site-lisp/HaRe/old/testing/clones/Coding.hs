module Coding where

data Tree = Leaf Char Int | Node Int Tree Tree

-- The types of bits, Huffman codes and tables of Huffman codes.	

data Bit = L | R deriving (Eq,Show)

type HCode = [Bit]

type Table = [ (Char,HCode) ]

codeMessage :: Table -> [Char] -> HCode

codeMessage tbl = concat . map (lookupTable tbl)

-- lookupTable looks up the meaning of an individual char in
-- a Table.			

lookupTable :: Table -> Char -> HCode

lookupTable [] c = error "lookupTable"
lookupTable ((ch,n):tb) c
  | (ch==c)     = n			
  | otherwise   = lookupTable tb c	


-- Decode a message according to a tree.				
-- 								
-- The first tree arguent is constant, being the tree of codes;	
-- the second represents the current position in the tree relative	
-- to the (partial) HCode read so far.				 


decodeMessage :: Tree -> HCode -> String

decodeMessage tr
  = decodeByt tr
    where

    decodeByt (Node n t1 t2) (L:rest)
	= decodeByt t1 rest

    decodeByt (Node n t1 t2) (R:rest)
	= decodeByt t2 rest

    decodeByt (Leaf c n) rest
	= c : decodeByt tr rest

    decodeByt t [] = []