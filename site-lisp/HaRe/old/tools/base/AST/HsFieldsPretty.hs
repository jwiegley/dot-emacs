-- Labelled fields, used in patterns and expressions
module HsFieldsPretty where
import HsFieldsStruct
import PrettyPrint

instance (Printable i,Printable p) => Printable (HsFieldI i p) where
  ppi (HsField n p) = wrap n <+> equals <+> p
  ppiList = fsep . punctuate comma
