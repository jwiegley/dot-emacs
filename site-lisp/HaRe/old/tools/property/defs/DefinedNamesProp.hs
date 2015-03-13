module DefinedNamesProp where
import DefinedNames
import DefinedNamesPropStruct()
import DefinedNamesBase()
import PropSyntax(HsDeclI,Prop,prop,mapProp,struct,listBase)
import TiNames(ValueId)

instance DefinedNames i (HsDeclI i) where
  definedNames = definedNamesRec

instance ClassMethods i (HsDeclI i) where
  classMethods c cnt = listBase (classMethods c cnt) . struct

instance ValueId i => AddName i (HsDeclI i) where addName = addNameRec

instance MapDefinedNames i (HsDeclI i) where mapDefinedNames = mapDefinedNamesRec
{-
instance DefinedNames i (HsPatI i) where
  definedNames = definedNamesRec
-}

instance (DefinedNames i b,DefinedNames i p) => DefinedNames i (Prop b p) where
  definedNames = prop definedNames definedNames

instance (ClassMethods i b,ClassMethods i p) => ClassMethods i (Prop b p) where
  classMethods c cnt = prop (classMethods c cnt) (classMethods c cnt)

instance (AddName i b,AddName i p) => AddName i (Prop b p) where
  addName = mapProp addName addName

instance (MapDefinedNames i b,MapDefinedNames i p)
      => MapDefinedNames i (Prop b p) where
  mapDefinedNames f = mapProp m m
    where m x = mapDefinedNames f x
