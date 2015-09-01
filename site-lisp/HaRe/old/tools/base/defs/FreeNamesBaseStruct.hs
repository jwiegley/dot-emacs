module FreeNamesBaseStruct where

import FreeNames
import DefinedNames(DefinedNames)

import BaseSyntax
import Lists((\\\))
import Data.List(nub)
import TypedIds
--import AccList(accList)

import HsName


-- modules (computes names that need to be imported)

instance FreeNames i ds => FreeNames i (HsModuleI m i ds) where
  freeNames = freeNames . hsModDecls

{-+
For patterns, #freeNames# should return the identifiers that appear in the
pattern, but are not bound by the pattern, i.e., constructors and field labels.
-}
instance FreeNames i p => FreeNames i (PI i p) where
    freeNames p =
      case p of
        HsPRec i fs -> con i : freeNames fs
        _           -> accPI2 (const id) ((:).con) ((++).freeNames) p []

-- freeNotDef p = freeNames p \\\ defs p

-- record fields
instance FreeNames i p => FreeNames i (HsFieldI i p) where
  freeNames (HsField f p) = field f:freeNames p


-- rhss
instance FreeNames i e => FreeNames i (HsRhs e) where
    freeNames x = accRhs (++) (mapRhs freeNames x) []

-- alts
instance (FreeNames i e, FreeNames i p, FreeNames i ds,
         DefinedNames i ds, DefinedNames i p)
      => FreeNames i (HsAlt e p ds) where
    freeNames (HsAlt _ p rhs ds) 
        = freeNames p ++ (freeNames (rhs,ds) \\\ defs (ds,p))

-- stmts
instance ( FreeNames i e, FreeNames i p, FreeNames i ds
         , DefinedNames i p, DefinedNames i ds
         ) => FreeNames i (HsStmt e p ds) where
    freeNames stmt =
      case stmt of
        HsGenerator _ p e stmt -> freeNames (p,e) ++ (freeNames stmt \\\ defs p)
        HsQualifier   e stmt -> freeNames (e,stmt)
        HsLetStmt    ds stmt -> freeNames (stmt,ds) \\\ defs ds
        HsLast        e      -> freeNames e


-- Since this is not a strictly accumulating function, there are many cases
-- in which accE can not be used...

-- exps
instance ( FreeNames i e, FreeNames i p, FreeNames i ds
         , FreeNames i t, FreeNames i c 
         , DefinedNames i p, DefinedNames i ds 
         ) => FreeNames i (EI i e p ds t c) where
    freeNames e =
      case e of
        HsLambda ps e          -> freeNames ps ++ (freeNames e \\\ defs ps)
        HsLet ds e             -> freeNames (e,ds) \\\ defs ds
        HsId n                 -> [val n]
        HsInfixApp x op z      -> val op : freeNames (x,z)
        HsCase e alts          -> freeNames (e,alts)
        HsDo stmts             -> freeNames stmts
        HsLeftSection x op     -> val op : freeNames x
        HsRightSection op y    -> val op : freeNames y
        HsListComp stmts       -> freeNames stmts
	HsRecConstr s n fs     -> con n : freeNames fs
	HsRecUpdate s e fs     -> freeNames (e,fs)

        _                      ->
            accEI bug descend bug bug descend descend e []
        where
	descend s = ((++).freeNames) s
        bug = error "freeNames at E ...: should have been handled"

-- matches
instance ( FreeNames i e, FreeNames i p, FreeNames i ds
         , DefinedNames i ds, DefinedNames i p 
         ) => FreeNames i (HsMatchI i e p ds) where
    freeNames (HsMatch _ n ps rhs ds) =
        freeNames ps ++ ((freeNames (rhs,ds) \\\ defs ps) 
                                \\\ (val (HsVar n) : defs ds))

-- decls 
instance ( FreeNames i e, FreeNames i p, FreeNames i ds, FreeNames i t
         , FreeNames i c, FreeNames i tp
         , DefinedNames i p, DefinedNames i ds 
         ) => FreeNames i (DI i e p ds t c tp) where
    freeNames d =
	case d of
	  HsTypeDecl s tps t             -> freeNames t \\\ freeNames tps
	  HsNewTypeDecl s ctx tps cd drv -> dataNames ctx tps [cd] drv
	  HsDataDecl s ctx tps cds drv   -> dataNames ctx tps cds  drv
	  HsClassDecl s c tp fdeps ds    -> freeNames (c,ds) \\\ freeNames tp -- hmm
	  HsInstDecl s optn c tp ds      -> freeNames ((c,tp),ds) \\\ freeVars tp -- hmm
	  HsDefaultDecl s t              -> freeNames t
	  HsTypeSig s nms c tp           -> freeCons (c,tp)
	  HsFunBind s matches            -> freeNames matches
	  HsPatBind s p rhs ds           -> freeNames p ++ 
					      (freeNames (rhs,ds) \\\ defs (p,ds))
	  HsInfixDecl   s fixity names   -> []

  --      HsPrimitiveTypeDecl s cntxt nm   ->
  --      HsPrimitiveBind s nm t           ->

	  -- TODO
	  _                               -> []
      where
        dataNames ctx tps cds drv =
          nub (map tcon drv++freeNames (ctx,cds)) \\\ freeNames tps

instance (FreeNames i t,FreeNames i c) => FreeNames i (HsConDeclI i t c) where
  freeNames cd =
    case cd of 
      HsConDecl s is c n args -> freeNames (c,args) \\\ map tvar is
      HsRecDecl s is c n fields -> freeNames (c,map snd fields) \\\ map tvar is

instance FreeNames i t => FreeNames i (HsBangType t) where
  freeNames = freeNames . unbang

instance FreeNames i t => FreeNames i (TI i t) where
  freeNames t =
    case t of
      HsTyVar v -> [tvar v]
      HsTyCon v -> [tcon v]
      HsTyForall xs ps t -> freeNames (ps,t) \\\ map tvar xs
      _ -> crushT freeNames t


-- utils ---------------------------------------

field = var -- hmm!!
