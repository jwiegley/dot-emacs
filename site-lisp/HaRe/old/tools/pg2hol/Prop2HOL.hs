
-- $Id: Prop2HOL.hs,v 1.7 2001/10/17 21:37:51 hallgren Exp $

module Prop2HOL(prop2HOL) where

import Syntax
import SCC
import PrettyPrint
import HOLOps


prop2HOL :: HsModuleR -> Doc
prop2HOL = module2HOL

module2HOL :: HsModuleR -> Doc
module2HOL (HsModule m Nothing imports {- infixes -} decls)
    = fsep [ vcat $ map import2HOL imports,
--           vcat $ map infix2HOL infixes,
             vcat $ map hsDecl2HOL decls ]
--      where (dss, _) = bindingGroups decls
module2HOL (HsModule m (Just exports) imports {- infixes -} decls)
    = fsep [ vcat $ map export2HOL exports,
             vcat $ map import2HOL imports,
--           vcat $ map infix2HOL infixes,
             vcat $ map hsDecl2HOL decls ]
--      where (dss, _) = bindingGroups decls

export2HOL _ = notsupported0 "export declaration"

import2HOL _ = notsupported0 "import declaration"

infix2HOL (HsInfixDecl loc fixity ops) = notsupported loc "infix declaration"

decls2HOL :: [HsDecl] -> Doc
decls2HOL [] = empty
decls2HOL ds =
    vcat $ (text "let" <+> dhol :
            map (\dhol -> text "and" <+> dhol) dhols)
    where (dhol:dhols) = map hsDecl2HOL ds

hsDecl2HOL :: HsDecl -> Doc
hsDecl2HOL (Dec (HsTypeDecl loc ((Typ (HsTyCon con)):params) t))          
    -- notsupported loc "type synonym declaration"
    = blankline $ from loc
      $$ (text "Hol_datatype" <+>
          (backQuotes $
           ppi con <+> equals <+> hsType2HOL [con] t))
      $$ handleThm (text "Type synonym" <+> ppi con)
hsDecl2HOL (Dec (HsNewTypeDecl loc c ((Typ (HsTyCon con)):params) t ders))
    -- notsupported loc "newtype declaration"
    = blankline $ from loc
      $$ (text "Hol_datatype" <+>
          (backQuotes $
           ppi con <+> equals <+> hsConDecl2HOL [con] t))
      $$ handleThm  (text "Newtype" <+> ppi con)
hsDecl2HOL (Dec (HsDataDecl loc c ((Typ (HsTyCon con)):params) summands ders))
    = blankline $ from loc
      $$ (text "Hol_datatype" <+>
          (backQuotes $
           ppi con <+> equals <+>
           foldr1 (\d d' -> d $$ char '|' <+> d')
                  (map (hsConDecl2HOL [con]) summands)))
      $$ handleThm  (text "Datatype" <+> ppi con)
hsDecl2HOL (Dec (HsTypeSig loc nms c t))  
    = notsupported loc "type signature declaration"
hsDecl2HOL (Dec (HsFunBind loc ms))
    = blankline $ from loc
      $$ (text "val" <+> ppi fun <> text "_def" <+> equals <+>
          text "Define" <+>
          (backQuotes $
           foldr1 (\d d' -> parens d <+> text "/\\"
                            $$ d')
                  (map hsMatch2HOL ms)))
      $$ handleThm  (text "Function" <+> ppi fun)
    where (HsMatch _ fun _ _ _):_ = ms
hsDecl2HOL (Dec (HsPatBind loc (Pat (HsPId (HsVar v))) rhs ds))
    = blankline $ from loc
      $$ (text "val" <+> ppi v <> text "_def" <+> equals <+>
          text "Define" <+>
          (backQuotes $
           funRhs2HOL loc (ppi v) rhs ds))
      $$ handleThm  (text "CAF" <+> ppi v)
hsDecl2HOL (Dec (HsPatBind loc p rhs ds))
    = notsupported loc "pattern binding"
hsDecl2HOL (Dec (HsClassDecl loc c tp ds))
    = notsupported loc "class declaration"
hsDecl2HOL (Dec (HsInstDecl loc c tp ds))
    = notsupported loc "instance declaration"
hsDecl2HOL (Dec (HsDefaultDecl loc t))
    = notsupported loc "default declaration"
hsDecl2HOL (Dec (HsPrimitiveTypeDecl loc cntxt nm))
    = notsupported loc "Hugs-style primitive type declaration"
hsDecl2HOL (Dec (HsPrimitiveBind loc nm t))
    = notsupported loc "Hugs-style primitive type declaration"
hsDecl2HOL (PropDec (HsProperty loc (ns @ (prop:_)) e))
    = blankline $ from loc
      $$ (holComment $ text "Property:" <+> pns)
      $$ fsep [ text "val prop_" <> pprop <+> equals,
                letNest $ parens $ backQuotes $ backQuotes $ hsExp2HOL e ]
      $$ handleTerm (text "Property" <+> pprop)
      where pns = sep $ map ppi ns
            pprop = ppi prop        


hsConDecl2HOL :: [HsName] -> HsConDecl HsType  -> Doc 
hsConDecl2HOL excl (HsConDecl loc con params)
    = hsName2HOL con <+> ps
      where ps = case params of
                 [] -> empty
                 xs -> text "of" <+>
                       (hsep $ punctuate (text " =>") $
                        map (hsType2HOL excl . hsBangType2Type) xs)
hsConDecl2HOL excl (HsRecDecl loc _ _)
    = notsupported loc "record declaration"

hsMatch2HOL :: HsMatch HsExp HsPat [HsDecl] -> Doc
hsMatch2HOL (HsMatch loc fun ps rhs ds)
    = funRhs2HOL loc (wrap fun <+> (fsep $ map wrap ps)) rhs ds

funRhs2HOL :: SrcLoc -> Doc -> HsRhs HsExp -> [HsDecl] -> Doc
funRhs2HOL loc lhs (HsBody e)   ds =
    fsep [ lhs <+> equals,
	   funNest $
           hsLet2HOL ds e ]
funRhs2HOL loc lhs (HsGuard gs) ds =
    -- should convert guards to ifs, but need to factor in other function
    -- branches, since a missing "otherwise" or "True" leaves us without an
    -- else branch.  This involves some of the patterm match compilation
    -- machinery.  This may be needed anyway, since it's not clear how complex
    -- case expressions can be.
    notsupported loc "guarded function/CAF definiton"

hsLet2HOL :: [HsDecl] -> HsExp -> Doc
hsLet2HOL []     e = hsExp2HOL e
hsLet2HOL (d:ds) e = fsep [ text "let" <+> hsLetDecl2HOL d,
                            text "in" $$
                            (letNest $ hsLet2HOL ds e) ]
    
hsLetDecl2HOL (Dec (HsFunBind loc [m]))    =
    hsMatch2HOL m
hsLetDecl2HOL (Dec (HsFunBind loc ms))     =
    notsupported loc "function definitions with many cases in lets"
hsLetDecl2HOL (Dec (HsPatBind loc p rhs ds)) =
    funRhs2HOL loc (wrap p) rhs ds
hsLetDecl2HOL _                              =
    notsupported0 "non-function/pattern definitions in lets"

--hsExp2HOL :: HsExp -> Doc    
hsExp2HOL (Exp (HsId n))                 = hsIdent2HOL n
hsExp2HOL (Exp (HsLit l))                = ppi l
hsExp2HOL (Exp (HsInfixApp x (HsVar (UnQual "$")) y)) =
    fsep [ hsExp2HOL x, letNest $ parens $ hsExp2HOL y ]
hsExp2HOL (Exp (HsInfixApp x op y))      = hsInfixOp2HOL
                                               (hsOp2HOL op)
                                               (hsExp2HOL x)
                                               (letNest $ hsExp2HOL y)
hsExp2HOL (Exp (HsApp x y))              = fsep [ hsExp2HOL x,
                                                  letNest $ hsExp2HOL y ]
hsExp2HOL (Exp (HsNegApp x))             = char '-' <> hsExp2HOL x
hsExp2HOL (Exp (HsLambda ps e))          = fsep
                                           [ char '\\' <+>
					     sep (map (hsPat2HOL wrap) ps) <+>
				             char '.',
					     letNest $ hsExp2HOL e ]
hsExp2HOL (Exp (HsLet ds e))             = hsLet2HOL ds e
hsExp2HOL (Exp (HsIf x y z))             = text "if" <+> hsExp2HOL x <+>
                                           text "then"
				           $$ (letNest $ hsExp2HOL y)
				           $$ text "else"
				           $$ (letNest $ hsExp2HOL z)
hsExp2HOL (Exp (HsCase e alts))          =
    text "case" <+> hsExp2HOL e <+> text "of"
    $$ (vcat $ (nest 2 halt) : map (char '|' <+>) talt)
    where (halt:talt) = map hsAlt2HOL alts
hsExp2HOL (Exp (HsDo stmts))             =
    notsupported0 "do notation"
hsExp2HOL (Exp (HsTuple xs))             = ppiFTuple xs
hsExp2HOL (Exp (HsList xs))              = ppiList xs
hsExp2HOL (Exp (HsParen e))              = parens $ hsExp2HOL e
hsExp2HOL (Exp (HsLeftSection x op))     =
    parens $
    fsep [ char '\\' <+> ppi y <+> char '.',
           hsInfixOp2HOL (hsOp2HOL op) (hsExp2HOL x) (ppi y) ]
    where y :: HsExp
          y = hsEVar $ UnQual "_y" -- Must be replaced by unique name
hsExp2HOL (Exp (HsRightSection op y))    =
    parens $
    fsep [ char '\\' <+> ppi x <+> char '.',
           hsInfixOp2HOL (hsOp2HOL op) (ppi x) (hsExp2HOL y) ]
    where x :: HsExp
	  x = hsEVar $ UnQual "_x" -- Must be replaced by unique name
--hsExp2HOL (Exp (HsRecConstr n []))       = -- "A{}" is NOT the same as "A"...
--    notsupported0 "record construction"
hsExp2HOL (Exp (HsRecConstr n upds))     =
    notsupported0 "record construction"
hsExp2HOL (Exp (HsRecUpdate e []))       =
    notsupported0 "record update"
hsExp2HOL (Exp (HsRecUpdate e upds))     =
    notsupported0 "record update"
hsExp2HOL (Exp (HsEnumFrom x))           =
    notsupported0 "numeric enumeration"
hsExp2HOL (Exp (HsEnumFromTo x y))       =
    notsupported0 "numeric enumeration"
hsExp2HOL (Exp (HsEnumFromThen x y))     =
    notsupported0 "numeric enumeration"
hsExp2HOL (Exp (HsEnumFromThenTo x y z)) =
    notsupported0 "numeric enumeration"
hsExp2HOL (Exp (HsListComp stmts))       =
    notsupported0 "list comprehension"
hsExp2HOL (Exp (HsExpTypeSig s e c t))   =
    notsupported0 "type signature"
hsExp2HOL (Exp (HsAsPat n p))            =
    error "hsExp2HOL: pattern exp in expression"
hsExp2HOL (Exp (HsWildCard))             =
    error "hsExp2HOL: pattern exp in expression"
hsExp2HOL (Exp (HsIrrPat p))             =
    error "hsExp2HOL: pattern exp in expression"
hsExp2HOL (PropExp (HsQuant q ps e))       =
    fsep [ hsQuantifier2HOL q <+>
           sep (map (hsPat2HOL wrap) ps) <+>
           char '.',
           letNest $ hsExp2HOL e ]

hsAlt2HOL (HsAlt loc p rhs ds) =
    fsep [ hsPat2HOL wrap p, text "=>", caseRhs2HOL loc rhs ds ]

caseRhs2HOL loc (HsBody e)   ds =
    hsLet2HOL ds e
caseRhs2HOL loc (HsGuard gs) ds =
    -- should convert guards to ifs, but need to factor in other function
    -- branches, since a missing "otherwise" or "True" leaves us without an
    -- else branch.  This involves some of the patterm match compilation
    -- machinery.  This may be needed anyway, since it's not clear how complex
    -- case expressions can be.
    notsupported loc "guarded pattern in case expression"

hsQuantifier2HOL HsPropForall        = char '!'
hsQuantifier2HOL HsPropExists        = char '?'
hsQuantifier2HOL HsPropForallDefined = char '!' <+>
                                       (holComment $ text "defined")
hsQuantifier2HOL HsPropExistsUnique  = text "?!"

hsPat2HOL :: (HsPat -> Doc) -> HsPat -> Doc
hsPat2HOL ppf (Pat (HsPId id))             = ppi id
hsPat2HOL ppf (Pat (HsPLit lit))           = ppi lit
hsPat2HOL ppf (Pat (HsPNeg p))             = notsupported0 "negation pattern"
hsPat2HOL ppf (Pat (HsPInfixApp p1 op p2)) = fsep [ ppi op, ppf p1, ppf p2 ]
hsPat2HOL ppf (Pat (HsPApp id ps))         = fsep (ppi id : map ppf ps)
hsPat2HOL ppf (Pat (HsPTuple ps))          = ppiTuple ps
hsPat2HOL ppf (Pat (HsPList ps))           = ppiList ps
hsPat2HOL ppf (Pat (HsPParen p))           = parens $ ppi p
hsPat2HOL ppf (Pat (HsPRec _ _))           = notsupported0 "record pattern"
hsPat2HOL ppf (Pat (HsPRecUpdate _ _))     = notsupported0 "record pattern"
hsPat2HOL ppf (Pat (HsPAsPat id p))        = parens $
                                             ppi id <+> text "as" <+> ppf p
hsPat2HOL ppf (Pat (HsPWildCard))          = text "_dummy"
hsPat2HOL ppf (Pat (HsPIrrPat p))          = ppf p
hsPat2HOL ppf (PropPat (HsPatTypeSig p c t)) = ppf p

hsType2HOL :: [HsName] -> HsType -> Doc 
hsType2HOL excl (Typ typ)
    = case typ of
        HsTyVar v     -> quote <> hsName2HOL v
        HsTyCon c     -> hsTyCon2HOL c
        HsTyApp (t1@(Typ (HsTyCon c))) t2
            | c `elem` excl -> hsType2HOL excl t1
        HsTyApp t1 t2 -> parens (hsType2HOL excl t2) <+> hsType2HOL excl t1
        HsTyTuple ts  -> hsep $ punctuate (text " #")
                              $ map (hsType2HOL excl) ts
        HsTyFun t1 t2 ->
            hsType2HOL excl t1 <+> text "->" <+> hsType2HOL excl t2

hsBangType2Type (HsBangedType t)   = t
hsBangType2Type (HsUnBangedType t) = t -- ignore strictness annotations

hsIdent2HOL :: HsIdent -> Doc
hsIdent2HOL = snd . hsOp2HOL

hsInfixOp2HOL (inf, op) x y | inf       = fsep [ x, op, y ]
                            | otherwise = fsep [ op, x, y ]

hsOp2HOL (HsCon (id @ (Qual _ n))) =
    case getHOLOp n of
    Just (inf, holop) -> (inf,   text holop)
    Nothing           -> (False, hsName2HOL id)
hsOp2HOL (HsCon (id @ (UnQual n))) =
    case getHOLOp n of
    Just (inf, holop) -> (inf,   text holop)
    Nothing           -> (False, hsName2HOL id)
hsOp2HOL (HsVar (id @ (Qual _ n))) =
    case getHOLOp n of
    Just (inf, holop) -> (inf,   text holop)
    Nothing           -> (False, hsName2HOL id)
hsOp2HOL (HsVar (id @ (UnQual n))) =
    case getHOLOp n of
    Just (inf, holop) -> (inf,   text holop)
    Nothing           -> (False, hsName2HOL id)

hsTyCon2HOL (id @ (Qual _ n)) =
    case getHOLTyCon n of
    Just holtycon -> text holtycon
    Nothing       -> hsName2HOL id
hsTyCon2HOL (id @ (UnQual n)) =
    case getHOLTyCon n of
    Just holtycon -> text holtycon
    Nothing       -> hsName2HOL id

hsName2HOL :: HsName -> Doc 
hsName2HOL (UnQual n)        = text n 
hsName2HOL (id @ (Qual _ n)) = text n <+> (holComment $ ppi id)

holComment d = text "(*" <+> d <+> text "*)"
from loc     = holComment $ text "From" <+> ppi loc <+> char ':'

notsupported loc msg
    = holComment $
      text "Not supported:" <+> text msg <+> text "from" <+> ppi loc
notsupported0 msg
    = holComment $ text "Not supported:" <+> text msg

handle failed backup =
    text "handle e =>" <+>
    (parens $
     (vcat [ text "print" <+>
             (doubleQuotes $ (failed <+> text "failed with exception"))
             <> semi,
             text "Exception.print_HOL_ERR e" <> semi,
             backup 
           ])
    )
    $$
    semi

handleThm  failed = handle failed (text "dummyThm")
handleTerm failed = handle failed (text "dummyTerm")
