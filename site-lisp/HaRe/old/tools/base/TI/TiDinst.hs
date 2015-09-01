{-+
Some definitions to support type annotations and
the dictionary translation for base language declarations (the D structure).
-}
module TiDinst where
import Data.Maybe(isJust)

import HsDeclStruct
import HsDeclMaps(mapDI)
import HsGuardsStruct(HsRhs(..))
import HasBaseStruct
import SubstituteBaseStruct
import Substitute
import TI hiding (Subst)
import TiDkc(Dinst)
import MUtils(( # ))

instance (Types i e,Types i p,Types i ds)
      => Types i (Dinst i e p ds) where
  tmap f  = mapDI id (tmap f) (tmap f) (tmap f) f (map f) id

instance (HasId i p,HasCoreSyntax i p) => HasAbstr i (Dinst i e p ds) where
  abstract [] d = d
  abstract xs d =
    case d of
      HsFunBind s matches  -> HsFunBind s (abstract xs matches)
      HsPatBind s p rhs ds ->
        case isVar p of
	  Just x -> HsFunBind s [abstract xs (HsMatch s x [] rhs ds)]
	  _ -> error (show s++": Bug in TiD.hs: tried to overload a pattern binding.")
      _ -> d
  --  HsPrimitiveTypeDecl s cntxt nm   ->
  --  HsPrimitiveBind s nm t           ->

instance (HasBaseStruct d (Dinst i e p ds),HasCoreSyntax i p,HasDef ds d,
	  Eq i,FreeNames i e,FreeNames i ds,FreeNames i p,
	  HasId i e,MapExp e ds,Subst i e,
	  AddDeclsType i ds)
         => HasLocalDef i e (Dinst i e p ds) where
  letvar x@(i:>:_) e d =
    case d of
      HsFunBind s matches  -> HsFunBind s (letvar x e matches)
      HsPatBind s p rhs ds ->
	  if in_p || HsVar i `elem` freeVars (rhs,ds)
          then if in_p || not is_id
	       then -- No substitution in patterns yet (for overloaded literals)
                    HsPatBind s p rhs (appendDef (letvarD s x e) ds)
	       else esubst1 var e i d
	  else d
	where
	  in_p = HsVar i `elem` freeVars p
	  is_id = isJust (isId e)
      _ -> d -- !!

instance HasCoreSyntax i p => HasAbstr i (HsMatchI i e p ds) where
  abstract xs (HsMatch s n ps rhs ds) = HsMatch s n (map var xs++ps) rhs ds

instance (HasBaseStruct d (Dinst i e p ds),HasCoreSyntax i p,HasDef ds d,
	  Eq i,FreeNames i e,FreeNames i ds,FreeNames i p,
	  HasId i e,MapExp e ds,Subst i e,
	  AddDeclsType i ds)
          => HasLocalDef i e (HsMatchI i e p ds) where
  letvar x@(i:>:_) e m@(HsMatch s n ps rhs ds) =
      if in_p || HsVar i `elem` freeVars (rhs,ds)
      then if in_p || not is_id
           then m' -- No substitution in patterns yet (for overloaded literals)
           else esubst1 var e i m
      else m
    where
      m' = HsMatch s n ps rhs (appendDef (letvarD s x e) ds)
      in_p = HsVar i `elem` freeVars ps
      is_id = isJust (isId e)

letvarD s (x:>:t) e = addDeclsType ([],[HsVar x:>:mono t]) $
		      oneDef (hsSimpleBind s x e)

hsSimpleBind s x e = hsSimpleBind' s x e noDef
hsSimpleBind' s x e = hsPatBind s (var x) (HsBody e)
