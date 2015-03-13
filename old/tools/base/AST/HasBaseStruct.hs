{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies  #-}
{-# LANGUAGE FlexibleContexts  #-}
module HasBaseStruct where
import BaseSyntaxStruct
import SpecialNames

class HasBaseStruct r base | r->base where
  base :: base -> r

class GetBaseStruct r base | r->base where
  basestruct :: r -> Maybe base


--instance HasBaseStruct rec base => HasBaseStruct [rec] [base] where
--  base = map base

-- Decl building
hsTypeDecl sloc tp hstype       = base $ HsTypeDecl sloc tp hstype
hsNewTypeDecl sloc c tp consdecl hsnames2
    = base $ HsNewTypeDecl sloc c tp consdecl hsnames2
hsDataDecl sloc c tp condecls names2
    = base $ HsDataDecl sloc c tp condecls names2
hsClassDecl sloc c typ fdeps decls = base $ HsClassDecl sloc c typ fdeps decls
hsInstDecl sloc optn c typ decls   = base $ HsInstDecl  sloc optn c typ decls
hsDefaultDecl sloc typ          = base $ HsDefaultDecl sloc typ
hsTypeSig sloc hsnames c t      = base $ HsTypeSig sloc hsnames c t
hsFunBind sloc hsmatches        = base $ HsFunBind sloc hsmatches
hsPatBind sloc pat rhs decls    = base $ HsPatBind sloc pat rhs decls
hsInfixDecl sloc fixity hsnames = base $ HsInfixDecl sloc fixity hsnames
hsPrimitiveTypeDecl sloc c name = base $ HsPrimitiveTypeDecl sloc c name 
hsPrimitiveBind sloc name t     = base $ HsPrimitiveBind sloc name t

hsId n                      = base $ HsId n
hsEVar name                 = base $ HsId $ HsVar name
hsECon name                 = base $ HsId $ HsCon name
hsLit sloc lit              = base $ HsLit sloc lit
hsInfixApp e1 op e2         = base $ HsInfixApp e1 op e2
hsApp e1 e2                 = base $ HsApp e1 e2
hsNegApp s e                = base $ HsNegApp s e
hsLambda pats e             = base $ HsLambda pats e
hsLet decls e               = base $ HsLet decls e
hsIf e1 e2 e3               = base $ HsIf e1 e2 e3
hsCase e alts               = base $ HsCase e alts
hsDo stmts                  = base $ HsDo stmts
hsTuple exps                = base $ HsTuple exps
hsList exps                 = base $ HsList exps
hsParen e                   = base $ HsParen e
hsLeftSection e op          = base $ HsLeftSection  e op
hsRightSection op e         = base $ HsRightSection op e
hsRecConstr sloc name fupds = base $ HsRecConstr sloc name fupds
hsRecUpdate sloc e fupds    = base $ HsRecUpdate sloc e fupds
hsEnumFrom e                = base $ HsEnumFrom e
hsEnumFromTo e1 e2          = base $ HsEnumFromTo e1 e2
hsEnumFromThen e1 e2        = base $ HsEnumFromThen e1 e2
hsEnumFromThenTo e1 e2 e3   = base $ HsEnumFromThenTo e1 e2 e3
hsListComp stms             = base $ HsListComp stms
hsExpTypeSig sloc e c t     = base $ HsExpTypeSig sloc e c t
hsAsPat hname e             = base $ HsAsPat hname e
hsWildCard                  = base  HsWildCard
hsIrrPat e                  = base $ HsIrrPat e

-- Pat building
hsPId n                     = base $ HsPId n
hsPVar n                    = base $ HsPId $ HsVar n
hsPCon n                    = base $ HsPId $ HsCon n
hsPLit sloc lit             = base $ HsPLit sloc lit
hsPNeg sloc lit             = base $ HsPNeg sloc lit
hsPSucc sloc n lit          = base $ HsPSucc sloc n lit
hsPInfixApp p1 op p2        = base $ HsPInfixApp p1 op p2
hsPApp hname pats           = base $ HsPApp hname pats
hsPTuple sloc pats          = base $ HsPTuple sloc pats
hsPList sloc pats           = base $ HsPList sloc pats
hsPParen p                  = base $ HsPParen p
hsPRec hname patfields      = base $ HsPRec hname patfields
hsPAsPat hname p            = base $ HsPAsPat hname p
hsPWildCard                 = base  HsPWildCard
hsPIrrPat p                 = base $ HsPIrrPat p


-- Kind building
kstar      = base Kstar
kpred      = base Kpred
karrow x y = base (Kfun x y)
kprop      = base Kprop -- P-Logic

-- Type building
hsTyFun t1 t2 = base $ HsTyFun t1 t2
--hsTyTuple ts = base $ HsTyTuple ts
hsTyTuple ts  = foldl hsTyApp (hsTyCon (tuple_tycon_name (length ts-1))) ts
hsTyApp f x   = base $ HsTyApp f x
hsTyVar name  = base $ HsTyVar name
hsTyCon name  = base $ HsTyCon name
hsTyForall xs ps t = base $ HsTyForall xs ps t

hsTyId (HsCon c) = hsTyCon c
hsTyId (HsVar v) = hsTyVar v


-- Added because of the stupid monomorphism restriction:
hsWildCard   :: HasBaseStruct exp (EI i e p ds t c) => exp
hsPWildCard  :: HasBaseStruct pat (PI i p) => pat
kstar, kpred, kprop :: HasBaseStruct kind (K k) => kind
