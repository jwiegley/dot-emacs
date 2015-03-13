{-+
This module defined various classes and auxiliary types that are used
throughout the type checker.
-}
module TiClasses where
import TiMonad(IM,KEnv)
import TiSolve(TypeConstraint)
import TiTypes
import HsLiteral(HsLiteral)
--import HasBaseStruct(hsIf)
--import DefinedNames(DefinedNames)
import TiKinds(KindConstraint)
import TiInstanceDB(Instance)
--import List(nub)
import MUtils
import AccList
--import Substitute
--import SrcLoc

type TypedDecls i ds = Typing ds (DeclsType i)
type TypedTopDecls i ds = Typing ds ([Instance i],DeclsType i)
type DeclsType i = ([TAssump i],[Assump i])

type TAssump i = Typing (HsIdentI i) (Kind,TypeInfo i)

nilDeclsType = ([],[]) -- ::DeclsType i

--(+++) :: DeclsType i->DeclsType i->DeclsType i
(xs1,ys1)+++(xs2,ys2) = (xs1++xs2,ys1++ys2)
concDeclsType = foldr (+++) nilDeclsType

class AddDeclsType i d | d->i where
  addDeclsType :: DeclsType i -> d -> d
  rmDeclsType :: d -> d

  addDeclsType _ d = d
  rmDeclsType = id

{-
Although their syntax are different, and they are type checked differently,
the base syntax uses *the same* type for, top level declarations,
local declarations, declarations in class definitions and declarations
in instance definitions. Obviously we can't use the same overloaded function
for type checking all of them...
-}
type CheckDecls i s r = s -> TI i (TypedDecls i r)
type CheckTopDecls i s r = s -> TI i (TypedTopDecls i r)
type CheckInstDecls i s r = [Assump i] -> s -> TI i r

class TypeCheckDecls i s r {-| s->r-} where
  tcTopDecls :: (s->s) -> CheckTopDecls i s r
  tcInstDecls :: CheckInstDecls i s r
   --,tcLocalDecls' --, tcClassDecls

  --tcLocalDecls' = tcTopDecls
tcLocalDecls ds = fmap (snd.snd) # tcTopDecls id ds
   -- discard instance db and kind env

class TypeCheckDecl i s r where
  tcDecl :: [Typed i (HsIdentI i)] -> s -> TI i r

class CheckRecursion i d where checkRecursion :: [d] -> TI i ()

type TI i = IM i (TypeConstraint i)
type KI i = IM i KindConstraint
class TypeCheck i s r {-| s->r-} where tc :: s -> TI i r
class KindCheck i t r | t->r where kc :: t -> KI i r

class DeclInfo i d | d->i where
  explicitlyTyped :: [Kinded (HsIdentI i)] -> [Typing (HsIdentI i) (TypeInfo i)] -> [Pred i] -> d -> DeclsType i
--isTypeDecl :: d -> Bool
  isUnrestricted :: Bool -> d -> Bool
  keepAmbigTypes :: d -> Bool

  keepAmbigTypes d = False

class HasMethodSigs ds where splitMethodSigs :: ds -> (ds,ds)
{-
class GetSigs i c tp ds | ds->i c tp where
  getSigs :: ds -> [(SrcLoc,[i],c,tp)]
-}
{-
instance KindCheck t r=> KindCheck [t] [r] where
  kc = mapM kc
  
instance (KindCheck t1 r1,
	  KindCheck t2 r2) => KindCheck (t1,t2) (r1,r2) where
  kc (t1,t2) = (,) # kc t1 <# kc t2
-}
--instance TypeCheck i s r => TypeCheck i [s] [r] where tc = mapM tc

class HasId i e | e->i where
  ident :: HsIdentI i -> e
  isId :: e -> Maybe (HsIdentI i)

var x = ident (HsVar x)
con c = ident (HsCon c)

isVar e = do HsVar x <- isId e
	     return x

--class HasLit e where lit :: HsLiteral -> e

class HasId i e => HasCoreSyntax i e | e->i where
  app :: e -> e -> e
  tuple,list :: [e] -> e
--paren :: e -> e

class HasTypeAnnot i e | e->i where
  typeAnnot :: e -> Type i -> e
  typeAnnot e t = e -- default: no decoration

--typedIf t cnd thn els = typeAnnot (hsIf cnd thn els) t

class HasCoreSyntax i e => HasTypeApp i e | e->i where
  spec :: HsIdentI i -> Scheme i -> [Type i] -> e
  spec x sc ts = ident x -- default: no decoration

class HasAbstr i e | e->i where
  abstract :: [i] -> e -> e

class (HasAbstr i s) => HasLocalDef i e s | s->e i where
  letvar :: Typing i (Type i) -> e -> s -> s
{-
smartLetvar x@(i:>:_) e =
    case isId e of
      Just _ -> esubst1 var e i
      _ -> letvar x e
-}
--letvar x e1 e2 = abstract [x] e2 `app` e1

instance HasAbstr i e => HasAbstr i [e] where
  abstract = map . abstract

instance HasLocalDef i e s => HasLocalDef i e [s] where
  letvar x e1 = map (letvar x e1)

infixr 5 `consDef`
class HasDef ds d | ds->d where
  nullDef :: ds -> Bool
  noDef :: ds
  consDef :: d -> ds -> ds
  appendDef :: ds -> ds -> ds
  filterDefs :: (d->Bool) -> ds -> ds
  toDefs :: [d] -> ds

  toDefs = foldr consDef noDef

concatDefs ds = foldr appendDef noDef ds
oneDef d = consDef d noDef

class HasDefs ds d | ds->d where fromDefs :: ds -> [d]
instance HasDefs [d] d where fromDefs = id

--class Decorate s i where decorate :: i -> s -> s

class EnvFrom ds env | ds->env where accEnv :: ds -> env -> env

envFrom ds = accEnv ds nilDeclsType

instance EnvFrom d env => EnvFrom [d] env where accEnv = accList accEnv
