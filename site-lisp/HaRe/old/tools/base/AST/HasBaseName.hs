{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module HasBaseName where
import HsName(Id,HsName,ModuleName)
import HsIdent

class HasBaseName ie ib | ie->ib           where getBaseName :: ie -> ib

instance HasBaseName Id     Id             where getBaseName = id
instance HasBaseName HsName HsName         where getBaseName = id
--instance HasBaseName ModuleName ModuleName where getBaseName = id

instance HasBaseName ie ib => HasBaseName (HsIdentI ie) (HsIdentI ib) where
  getBaseName = mapHsIdent getBaseName
