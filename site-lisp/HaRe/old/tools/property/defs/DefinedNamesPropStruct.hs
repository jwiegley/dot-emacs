module DefinedNamesPropStruct where
import DefinedNames
import HsPropStruct
import HsIdent
import SrcLocPretty(shLineCol)
import TiNames(ValueId,localVal')

instance DefinedNames i (PD i e t) where
  definedNames (HsPropDecl s n ns e) = [(HsCon n,propName)] -- hmm
  definedNames (HsAssertion s (Just n) pa) = [(HsCon n,assertionName)] -- hmm
  definedNames _ = []

instance ClassMethods i (PD i e t) where
  classMethods c _ _ = []		

instance ValueId i => AddName i (PD i e t) where
  addName (HsAssertion s Nothing pa) = HsAssertion s (Just (defaultName s)) pa 
    where
      defaultName s =
         localVal' ("UnnamedAssertion__"++shLineCol s) (Just s)
  addName d = d

propName = Property -- hmm, properties names are in a separate name space,
                    -- but data constructors can be used as properties...
assertionName = Assertion -- assertions can be used as properties too

instance MapDefinedNames i (PD i e t) where mapDefinedNames f = id
