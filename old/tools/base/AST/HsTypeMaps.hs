-- $Id: HsTypeMaps.hs,v 1.11 2004/12/03 07:49:43 hallgren Exp $

--- Maps for the T functor -----------------------------------------------------
module HsTypeMaps where

import HsTypeStruct
import AccList(accList)
import MUtils


mapTI idf = mapTI2 idf idf

mapTI2 :: (i1 -> i2) -> 
          (i1 -> i2) -> 
          (t1 -> t2) -> 
          TI i1 t1 -> TI i2 t2
mapTI2 vf cf tf ty =
  case ty of
    HsTyFun x y        -> HsTyFun (tf x) (tf y)
--  HsTyTuple ts       -> HsTyTuple (map tf ts)
    HsTyApp f x        -> HsTyApp (tf f) (tf x)
    HsTyVar nm         -> HsTyVar (vf nm)
    HsTyCon nm         -> HsTyCon (cf nm)
    HsTyForall xs ps t -> HsTyForall (map vf xs) (map tf ps) (tf t)

mapT = mapTI id

crushT tf (HsTyFun x y)  = tf [x, y]
--crushT tf (HsTyTuple ts) = tf ts
crushT tf (HsTyApp f x)  = tf [f, x]
crushT tf (HsTyVar nm)   = tf []
crushT tf (HsTyCon nm)   = tf [] 
crushT tf (HsTyForall xs ps t) = tf (ps++[t])   -- not sure if that's right /ISD  /TH


-- ********** IMPORTANT *************
-- Several functions of typechecking (generalization in particular) depend
-- upon the fact that seqT , accList, and accT visit nodes in order from 
-- LEFT-TO-RIGHT, If this is changed several things will not work correctly. 
-- YOU HAVE BEEN WARNED !!!

-- After talking to Mark, it seems that it is only important that the order is
-- consistent between application of the various functions to types.

seqTI ty =
  case ty of
    HsTyFun x y        -> HsTyFun # x <# y
--  HsTyTuple ts       -> HsTyTuple # sequence ts
    HsTyApp f x        -> HsTyApp # f <# x
    HsTyVar nm         -> HsTyVar # nm
    HsTyCon nm         -> HsTyCon # nm
    HsTyForall xs ps t -> HsTyForall # sequence xs <# sequence ps <# t

--seqT :: (Functor m, Monad m) => T (m t) -> m (T t)
seqT x = seqTI . mapTI return id $ x
    
accTI idf tf ty =
  case ty of
    HsTyFun x y        -> tf x . tf y      -- LEFT-TO-RIGHT here
--  HsTyTuple ts       -> accList tf ts 
    HsTyApp f x        -> tf f . tf x 
    HsTyVar nm         -> idf nm 
    HsTyCon nm         -> idf nm 
    HsTyForall xs ps t -> tf t . accList tf ps . accList idf xs


accT = accTI (curry snd)
