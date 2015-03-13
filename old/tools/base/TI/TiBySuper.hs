module TiBySuper where
import Prelude hiding (lookup)
import TiKinds
import TiKEnv(lookup)
import TiTypes
import TiNames
import TiClasses
import TiDefinedNames
import PrettyPrint
import MUtils
import TiSolve(matches,expandSynonyms)
import DefinedNamesBase()

-- Context reduction by using the superclass hierarchy.

{-
Dictionaries are transformed under the assumption that a dictionary for a
superclass can be obtained by applying a selector to the dictionary for
the subclass.

For example if we have d1::Ord a, then we can get d2::Eq a by d2=super1_Ord d1.
-}

bySuper env d@(de:>:dt) =
    (d:) #
    if null cs
    then return [] -- ill formed predicate (accepted as an exerimental feature)
    else case snd # lookup env c of
	   Just (Class [] ps _ ms) -> return [] -- speed hack, can be eliminated
	   Just (Class ctx0 ps _ ms) ->
	     do s <- dt `matches` st $ env
		concatMapM (bySuper env) (zipWith (sel s) [1..] ctx)
	     where
               ctx = map (expandSynonyms env) ctx0
                   -- Better to expand synonyms before adding class to env!!
	       st = tpat c (tdom ps)
               sel s n sup = (sne `app` de):>:supdt
	         where
	           supdt = apply s sup
		   sn = superName cn n
		   --sne = var sn -- without type annotations
		   sne = spec (HsVar sn) ssc (apply s (map tyvar (tdom ps)))
		   ssc = forall' ps ([]:=>funT [st,sup])
				    
  
	   Just i -> fail $ pp $ "Not a class:"<+>c<+>"in"<+>dt $$ show i
	   _      -> fail $ pp $ "Unknown class:"<+>c<+>"in"<+>dt
                               -- $$ "Env:"<+>env
  where
    c@(HsCon cn) = head cs
    tpat c vs = appT (ty c:map tyvar vs)

    cs = definedTypeNames dt
    
