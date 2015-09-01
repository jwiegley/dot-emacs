module DerivingEnum where
import DerivingUtils

deriveEnum stdnames src t@(_,TypeInfo{constructors=cs}) =
  do let pv = stdvalue stdnames mod_Prelude
     HsVar fromEnum <- pv "fromEnum"
     HsVar toEnum <- pv "toEnum"
     if isEnum cs
       then return (fromToEnum src fromEnum toEnum t id)
       else fail "Deriving Enum: the type is not an enumeration."

fromToEnum src fromEnum toEnum t@(_,TypeInfo{constructors=cs}) sig =
   [fromEnumDef,toEnumDef]
 where
  cns = zip [0..] cs

  fromEnumDef = fun src (map fromAlt cns)
  toEnumDef = fun src (map toAlt cns)

  fromAlt (n,ci) = alt1 src fromEnum (con c)
			((if n==0 then sig else id) (hsLit src (HsInt n)))
    where c = convCon t (conName ci)

  toAlt (n,ci) = alt1 src toEnum (hsPLit src (HsInt n)) (con c)
    where c = convCon t (conName ci)
