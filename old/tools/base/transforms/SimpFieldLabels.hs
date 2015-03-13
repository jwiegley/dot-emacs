module SimpFieldLabels(simpFieldLabels) where
import HsDeclStruct
import HsExpStruct
import HsFieldsStruct
import HsGuardsStruct
import HsLiteral
import SrcLoc1 as S(loc0,srcLoc)
import HasBaseStruct(basestruct,base,hsId,hsECon,hsApp,hsPApp,hsLit,hsPVar,hsEVar,hsCase)
import FieldSelectors(fieldSelectors)
import UniqueNames as U(orig,srcLoc)
import TiClasses(noDef,consDef,concatDefs)
import TypedIds
import QualNames
import PNT
--import TiPrelude(prelError)
import TiPNT()
import Substitute(mapExp)
import SimpPatMatch(conFields',confields,freshnames)
import PrettyPrint(pp,fsep,(<+>),(<>))

simpFieldLabels pErr = addFieldSelectors . simpAllFieldUpdates pErr

addFieldSelectors ds = concatDefs (map addFieldSelectors' ds)

addFieldSelectors' d =
  consDef d $
  case basestruct d of
    Just (HsDataDecl    s ctx tp cds drv) -> fieldSelectors noDef cds
    Just (HsNewTypeDecl s ctx tp cd drv)  -> fieldSelectors noDef [cd]
    _ -> noDef

simpAllFieldUpdates pErr m = mapExp (simpFieldUpdates pErr) m


simpFieldUpdates prelError e0 =
    case basestruct e of
      Just (HsRecConstr s c fields) | okConstr c fields
	  -> simpFieldConstruction bf s c fields
      Just (HsRecUpdate s e []) -> e
      Just (HsRecUpdate s e fields@(field1:_)) | okUpdate ucs
	  -> simpFieldUpdate bf s e ucs fields
	where
	  cfs = consfields s field1
	  ucs = updcons cfs (map (orig.fieldName) fields)

      _ -> e
  where
    bf = badfield prelError
    e = mapExp (simpFieldUpdates prelError) e0 -- simplify all subexpressions first

   --Only field labels declared with the specified constructor may be mentioned.
    okConstr c fields =
       map (orig.fieldName) fields `isSubsetOf` map orig (confields c)

    okUpdate = not . null

    consfields s field =
      case idTy (fieldName field) of
        FieldOf t ti ->
          [(con s ci t ti,conFields' ci)|ci<-constructors ti]
	_ -> []

    updcons cfs ufs = [c|c@(_,fs)<-cfs,ufs `isSubsetOf` map orig fs]

    con s ci t ti = PNT (mkUnqual (conName ci)) (ConstrOf t ti) (U.srcLoc s)

{-+
Haskell 98 Report, section 3.15.2 Construction Using Field Labels:
-}
simpFieldConstruction badfield s c fields =
    conApp c (map (pick badfield s fields (missingField badfield s)) fs)
  where
    fs = confields c

{-+
The funciton #pick# defined in section 3.15.2 of the Haskell 98 Report:
-}
pick badfield s fields d f =
  case [field|field<-fields,orig (fieldName field)==orig f] of
    [HsField _ e] -> e
    [] -> d f
    fs -> badfield $ pp $ dupmsg<+>f<+>"at"<+>
		          fsep (map (S.srcLoc.fieldName) fs) --compile-time error!
  where
    dupmsg = "H98 3.15 A field label may not be mentioned more than once:"

missingField badfield s f =
    -- compile-time error for strict fields, run-time error otherwise!
    badfield $ pp $ s<>":"<+>missing<+>f
  where
    missing ="H98 3.15 Fields not mentioned are initialized to _|_:"

{-+
Haskell 98 Report, section 3.15.3 Updates Using Field Labels:
-}
simpFieldUpdate badfield s e ufs fields =
    hsCase e (map branch ufs)
  where
    branch (c,fs) = HsAlt s (hsPApp c ps) (HsBody rhs) noDef
     where
      rhs = conApp c (zipWith (pick badfield s fields.const) es fs)
      es = map hsEVar vs
      ps = map hsPVar vs
      vs = freshnames s 'x' fs

---

badfield prelError msg = hsId prelError `hsApp` hsLit loc0 (HsString msg)

xs `isSubsetOf` ys = all (`elem` ys) xs

conApp c es = foldl hsApp (hsECon c) es
