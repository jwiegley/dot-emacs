{-# OPTIONS_GHC -cpp #-}
module Map60204 where


#if __GLASGOW_HASKELL__ >= 604 

import qualified Data.Map as M

insertM x t bs = M.insert x t bs 

emptyM = M.empty
lookupM x env = M.lookup x env
keysM env = M.keys env
elemsM env = M.elems env
toListM = M.toList
mapM' f bs = M.map f bs 

addListToM fm key_elt_pairs = addListTo_C (\ old new -> new) fm key_elt_pairs
 where 
   addListTo_C combiner fm key_elt_pairs
     = foldl add fm key_elt_pairs	-- foldl adds from the left
     where
      add fmap (key,elt) = M.insertWith combiner key elt fmap

addListTo_CM combiner fm key_elt_pairs
   = foldl add fm key_elt_pairs	 -- foldl adds from the left
   where
   add fmap (key,elt) = M.insertWith combiner key elt fmap

findWithDefaultM a k fm = M.findWithDefault a k fm

#else

import qualified Data.FiniteMap as M

insertM x t bs = M.addToFM bs x t 
emptyM = M.emptyFM
lookupM x env = M.lookupFM env x 
keysM env = M.keysFM env
elemsM env = M.eltsFM env
toListM = M.fmToList
addListToM fm key_elt_pairs = M.addListToFM fm key_elt_pairs
mapM' f bs  = M.mapFM (const f) bs
addListTo_CM combiner fm key_elt_pairs = M.addListToFM_C combiner fm key_elt_pairs
findWithDefaultM a k fm = M.lookupWithDefaultFM fm  a k

#endif 

