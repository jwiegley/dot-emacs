{-# OPTIONS -cpp #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module PPModules where

--import Modules
import CheckModules (ModSysErr(..))
import TypedIds
import HsIdentPretty
import Ents as E
import Relations
import PrettyPrint


instance Printable NameSpace where
    ppi ValueNames       = ppi "Value"
    ppi ClassOrTypeNames = ppi "TypeOrClass"

instance Printable i => Printable (IdTy i) where
    ppi (FieldOf x _)   = "field of" <+> x
    ppi (MethodOf x _ _)  = "method of" <+> x
    ppi (ConstrOf t tyinfo) = "con of" <+> tcon t -- <+> (constructors tyinfo)
    ppi (Class cnt ms)      = "Class" <+> cnt <+> ms
    ppi (Type tyInfo)   = "Type"  <+> tyInfo
    ppi t               = ppi (show t)

instance Printable i => Printable (TypeInfo i) where
    ppi tyInfo = constructors tyInfo <+> fields tyInfo

instance Printable i => Printable (ConInfo i) where
    ppi conInfo = con (conName conInfo)

instance Printable (ModSysErr) where
    ppi x = case x of
        UndefinedModuleAlias m  -> "Unknwon module alias" <+> "in export list"
        UndefinedExport a       -> "Undefined export entry" <+> a
        UndefinedSubExport x a  
            -> "Undefined subordinate" <+> a <+> "of" <+> x <+> "in export"
        AmbiguousExport a os    -> "Ambiguous export entry" <+> a <> ':' <+> os
        MissingModule m -> "Import from missing module" <+> m
        UndefinedImport m n     -> m <+> "does not export" <+> n
        UndefinedSubImport m x s 
            -> m <+> "does not export subordinate" <+> s <+> "of" <+> x
    


ppRel :: (Printable a, Printable b) => [(a,b)] -> Doc
ppRel = vcat . map f
    where
    f (x,y) = ppi x <+> kw "|->" <+> ppi y

instance (Show a, Show b, Printable a, Printable b) => Printable (Rel a b) where
--  ppi (Rel r) = ppRel r
    ppi r = ppRel (relToList r)

instance Printable n => Printable (Ent n) where
  ppi (E.Ent m n t) = hilite (m<>"."<>n)<>","<+>t
    where
      hilite = case t of
                 ConstrOf{} -> con
		 Type{}     -> tcon
		 Class{}    -> tcon
                 Assertion  -> con
                 Property   -> con
		 _          -> id

showRel r = show (relToList r)
readRel s = listToRel (read s)


#if __GLASGOW_HASKELL__<604
instance (Show a, Show b) => Show (Rel a b) where
    show r = show (relToList r)
#endif
{-
-- GHC 6.4 provides a Show instance but no Read instance.
-- This Read instance doesn't match the provided Show instance for Set :-(

instance (Ord a, Ord b, Read a, Read b) => Read (Rel a b) where
    readsPrec d s = [ (listToRel xs,a) | (xs,a) <- readsPrec d s ] 
-}
