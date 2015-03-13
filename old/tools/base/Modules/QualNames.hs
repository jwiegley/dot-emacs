{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module QualNames where

import HsName
import HsIdent
import Data.Maybe(isJust)

class QualNames qn m n | qn -> m n, m n -> qn where
  getQualifier  :: qn -> Maybe m
  getQualified  :: qn -> n
  mkUnqual      :: n -> qn
  mkQual        :: m -> n -> qn

isQual m    = isJust (getQualifier m)
isUnqual m  = not (isQual m)
qual m      = mkQual m . getQualified 
unqual m    = mkUnqual (getQualified m)



instance QualNames HsName ModuleName Id where
    getQualifier (Qual x _) = Just x
    getQualifier _          = Nothing
    
    getQualified (Qual _ x)   = x
    getQualified (UnQual x)   = x
 
    mkUnqual  = UnQual
    mkQual    = Qual
    
 
instance QualNames t m n => QualNames (HsIdentI t) m (HsIdentI n) where
    getQualifier                = getQualifier . getHSName
    getQualified                = mapHsIdent getQualified
 
    mkUnqual                    = mapHsIdent mkUnqual
    mkQual m                    = mapHsIdent (mkQual m)




