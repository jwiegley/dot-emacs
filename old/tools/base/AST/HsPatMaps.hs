-- $Id: HsPatMaps.hs,v 1.16 2005/05/31 02:25:25 hallgren Exp $

{-
   
   Standard maps for the P functor

-}

module HsPatMaps
where

import HsPatStruct
import HsFieldsMaps
import AccList(accList)
import MUtils
import HsIdent(mapHsIdent2,accHsIdent2,seqHsIdent)

mapPI idf = mapPI2 idf idf

mapPI2 :: (i1 -> i2) ->
          (i1 -> i2) ->
          (p1 -> p2) ->
          PI i1 p1 -> PI i2 p2
mapPI2 vf cf pf pat =
  case pat of
    HsPId n                -> HsPId (mapHsIdent2 vf cf n)
    HsPLit s l             -> HsPLit s l
    HsPNeg s l             -> HsPNeg s l
    HsPSucc s n l          -> HsPSucc s (vf n) l
    HsPInfixApp x op y     -> HsPInfixApp (pf x) (cf op) (pf y)
    HsPApp nm ps           -> HsPApp (cf nm) (map pf ps)
    HsPTuple s ps          -> HsPTuple s (map pf ps)
    HsPList  s ps          -> HsPList s (map pf ps)
    HsPParen p             -> HsPParen (pf p) 
    HsPRec nm fields       -> HsPRec (cf nm) (mapFieldsI vf pf fields)
    HsPAsPat nm p          -> HsPAsPat (vf nm) (pf p)
    HsPWildCard            -> HsPWildCard
    HsPIrrPat p            -> HsPIrrPat (pf p)


accPI idf = accPI2 idf idf

accPI2 :: (i -> b -> b) ->
          (i -> b -> b) ->
          (p -> b -> b) ->
          (PI i p) -> b -> b
accPI2 vf cf pf pat =
    case pat of
    HsPId n                -> accHsIdent2 vf cf n
    HsPLit s l             -> id 
    HsPNeg s l             -> id
    HsPSucc s n l          -> vf n
    HsPInfixApp x nm y     -> pf x . cf nm . pf y
    HsPApp nm ps           -> cf nm . accList pf ps
    HsPTuple s ps          -> accList pf ps
    HsPList  s ps          -> accList pf ps
    HsPParen p             -> pf p 
    HsPRec nm fields       -> cf nm . accFieldsI vf pf fields 
    HsPAsPat nm p          -> vf nm . pf p 
    HsPWildCard            -> id 
    HsPIrrPat p            -> pf p


accP :: (p -> b -> b) ->
        b ->
        (PI i p) ->
        b
accP pf = flip $ accPI (curry snd) pf


seqPI :: (Monad m,Functor m) => PI (m i) (m p) -> m (PI i p) 
seqPI pat =
   case pat of
     HsPId n                -> HsPId # seqHsIdent n
     HsPLit s l             -> return $ HsPLit s l
     HsPNeg s l             -> return $ HsPNeg s l
     HsPSucc s n l          -> HsPSucc s # n <# return l
     HsPInfixApp x op y     -> HsPInfixApp # x <# op <# y
     HsPApp nm ps           -> HsPApp # nm <# sequence ps
     HsPTuple s ps          -> HsPTuple s # sequence ps
     HsPList  s ps          -> HsPList s # sequence ps
     HsPParen p             -> HsPParen # p
     HsPRec nm fields       -> HsPRec # nm <# seqFieldsI fields
     HsPAsPat nm p          -> HsPAsPat # nm <# p
     HsPWildCard            -> return HsPWildCard
     HsPIrrPat p            -> HsPIrrPat # p
