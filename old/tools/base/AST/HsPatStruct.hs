{-# LANGUAGE DeriveDataTypeable  #-}
-- $Id: HsPatStruct.hs,v 1.29 2005/05/31 02:25:25 hallgren Exp $

module HsPatStruct where

import SrcLoc1
import HsIdent
import HsLiteral
import HsFieldsStruct

import Data.Generics

data PI i p
    = HsPId (HsIdentI i)         -- Variables and nullary constructors
    | HsPLit SrcLoc HsLiteral    -- Literal
    | HsPNeg SrcLoc HsLiteral    -- only numeric literals can be negated
    | HsPSucc SrcLoc i HsLiteral -- the horrible n+k pattern -- integer literal
    | HsPInfixApp p i p          -- For example fx:xs
    | HsPApp i [p]               -- Constructor applications
    | HsPTuple SrcLoc [p]        -- Tuple pattern, (p_1,...,p_n)
    | HsPList  SrcLoc [p]        -- List pattern, [p_1,...,p_n]
    | HsPParen p                 -- (p)
    | HsPRec i (HsFieldsI i p)   -- C{f_1=p_1,...,f_n=p_n}
    | HsPAsPat i p               -- x@p
    | HsPWildCard                -- _
    | HsPIrrPat p                -- ~p
      deriving (Ord, Read, Eq, Show, Data, Typeable)
      
{- instance (Eq i, Eq p) => Eq (PI i p) where
  HsPId i                == HsPId i1                    = i == i1
  HsPLit _ i             == HsPLit _ i1                 = i == i1
  HsPNeg _ i             == HsPNeg _ i1                 = i == i1
  HsPSucc _ i k          == HsPSucc _ i1 k1             = i == i1 && k == k1
  HsPInfixApp x op z     == HsPInfixApp x1 op1 z1        = x == x1 && op == op1 && z == z1
  HsPApp i xs            == HsPApp i1 xs1               = i == i1 && xs == xs1
  HsPTuple _ xs          == HsPTuple _ xs1              = xs == xs1
  HsPList _ xs           == HsPList _ xs1               = xs == xs1
  HsPParen p             == HsPParen p1                 = p == p1
  HsPRec i ups           == HsPRec i1 ups1              = i == i1 && ups == ups1
  HsPAsPat i p           == HsPAsPat i1 p1              = i == i1 && p == p1
  HsPWildCard            == HsPWildCard                 = True
  HsPIrrPat p            == HsPIrrPat p1                = p == p1 -}
