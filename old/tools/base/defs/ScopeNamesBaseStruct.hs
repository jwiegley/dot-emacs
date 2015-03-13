module ScopeNamesBaseStruct where
import ScopeNames
import DefinedNames
import DefinedNamesBaseStruct()
import FreeNames
import BaseSyntax
import MUtils
import EnvM

instance ScopeNames i e ds1 ds2
      => ScopeNames i e (HsModuleI m i ds1) (HsModuleI m (i,e) ds2) where
  scopeNames ext (HsModule s m e i ds) = HsModule s m # sc e <# sc i <# sc ds
    where sc x = scopeNames ext x

instance ScopeNames i e (HsExportSpecI m i) (HsExportSpecI m (i,e)) where
  scopeNames = scopeSpec

instance ScopeNames i e (HsImportSpecI i) (HsImportSpecI (i,e)) where
  scopeNames = scopeSpec

instance ScopeNames i e (HsImportDeclI m i) (HsImportDeclI m (i,e)) where
  scopeNames = scopeSpec -- uses the wrong environment!!!

scopeSpec ext spec = do env <- getEnv ; return (fmap (\i->(i,env)) spec)

pairEnv x = (,) x # getEnv

instance (Eq i,
	  ScopeNames i e e1 e2,
	  ScopeNames i e p1 p2,DefinedNames i p1,
	  ScopeNames i e ds1 ds2,DefinedNames i ds1,
	  ScopeNames i e t1 t2,FreeNames i t1,
	  ScopeNames i e c1 c2,FreeNames i c1)
       => ScopeNames i e (EI i e1 p1 ds1 t1 c1)
		         (EI (i,e) e2 p2 ds2 t2 c2) where
  scopeNames ext e =
    case e of
      HsLambda ps e        -> ex ps (HsLambda # sc ps <# sc e)
      HsLet ds e           -> ex ds (HsLet    # sc ds <# sc e)
      HsCase e alts        -> HsCase # sc e <# sc alts
      HsDo stmts           -> HsDo # sc stmts
      HsListComp stmts     -> HsListComp # sc stmts
      HsExpTypeSig s e c t -> HsExpTypeSig s # sc e <# ex (sc c) <# ex (sc t)
        where ex = exttvar ext (c,t)
      _ -> seqEI . mapEI pairEnv sc sc sc sc sc $ e
    where
      sc x = scopeNames ext x
      ex b = extdef ext b

extdef ext b = inModEnv . ext $ definedNames b
exttvar ext b = inModEnv . ext $ freeTyvars b
exttvs ext = inModEnv . ext . map (typedTvar . HsVar)

instance (ScopeNames i e e1 e2,
	  ScopeNames i e p1 p2,DefinedNames i p1,
	  ScopeNames i e ds1 ds2,DefinedNames i ds1)
      => ScopeNames i e (HsStmt e1 p1 ds1) (HsStmt e2 p2 ds2) where
  scopeNames ext stmt =
    case stmt of
      HsGenerator s p e stmt -> HsGenerator s # ex p (sc p) <# sc e <# ex p (sc stmt)
      HsQualifier e stmt -> HsQualifier # sc e <# sc stmt
      HsLetStmt ds stmt -> ex ds $ HsLetStmt # sc ds <# sc stmt
      HsLast e -> HsLast # sc e
    where
      sc x = scopeNames ext x
      ex b = extdef ext b

instance (ScopeNames i e e1 e2,
	  ScopeNames i e p1 p2,DefinedNames i p1,
	  ScopeNames i e ds1 ds2,DefinedNames i ds1)
	  => ScopeNames i e (HsAlt e1 p1 ds1) (HsAlt e2 p2 ds2) where
  scopeNames ext (HsAlt s p rhs ds) =
      HsAlt s # ex p (scopeNames ext p) <# r rhs <# r ds
    where
      r x = ex (p,ds) (sc x)
      sc x = scopeNames ext x
      ex b = extdef ext b

instance (ScopeNames i e e1 e2,
	  ScopeNames i e p1 p2,DefinedNames i p1,
	  ScopeNames i e ds1 ds2,DefinedNames i ds1)
	  => ScopeNames i e (HsMatchI i e1 p1 ds1) (HsMatchI (i,e) e2 p2 ds2) where
  scopeNames ext (HsMatch s i ps rhs ds) =
      HsMatch s # pairEnv i <# ex ps (scopeNames ext ps) <# r rhs <# r ds
    where
      r x = ex (ps,ds) (sc x)
      sc x = scopeNames ext x
      ex b = extdef ext b

instance ScopeNames i e e1 e2 => ScopeNames i e (HsRhs e1) (HsRhs e2) where
  scopeNames ext = seqRhs . mapRhs (scopeNames ext)

instance ScopeNames i e p1 p2
      => ScopeNames i e (PI i p1) (PI (i,e) p2) where
  scopeNames ext = seqPI . mapPI pairEnv (scopeNames ext)

instance (Eq i,
	  ScopeNames i e e1 e2,
	  ScopeNames i e p1 p2,DefinedNames i p1,
	  ScopeNames i e ds1 ds2,DefinedNames i ds1,
	  ScopeNames i e t1 t2,FreeNames i t1,
	  ScopeNames i e c1 c2,FreeNames i c1,
	  ScopeNames i e tp1 tp2,FreeNames i tp1)
       => ScopeNames i e (DI i e1 p1 ds1 t1 c1 tp1)
		         (DI (i,e) e2 p2 ds2 t2 c2 tp2) where
  scopeNames ext d =
      case d of
       HsTypeDecl s tps t             -> st tps
       HsNewTypeDecl s ctx tps cd drv ->
         HsNewTypeDecl s # mr ctx <# mr tps <# mr cd <# mapM pairEnv drv
           where mr x = exttvar ext tps $ m x
       HsDataDecl s ctx tps cds drv   ->
         HsDataDecl s # mr ctx <# mr tps <# mr cds <# mapM pairEnv drv
           where mr x = exttvar ext tps $ m x
       HsClassDecl s c tp fdeps ds    -> st tp -- hmm, fdeps
		         -- !!  ^^ Hmm, typevars in type sigs ds
       HsInstDecl s optn c tp ds      -> st (c,tp)
       HsTypeSig s nms c tp           -> st (c,tp)
       HsFunBind s ms -> HsFunBind s # mapM m ms
       HsPatBind s p rhs ds -> HsPatBind s # m p <# mr rhs <# mr ds
          where mr x = extdef ext ds $ m x
		--                ^^ not (p,ds)
		-- The variables in p are added to the environment before
		-- entering the declaration group this binding is part of,
		-- and should not be added again.
       HsPrimitiveTypeDecl s ctx tp   -> st tp
       HsPrimitiveBind s nm tp        -> st tp
       _ -> scAll
    where
      st tp = exttvar ext tp scAll
      scAll = seqDI $ mapDI pairEnv m m m m m m d
      m x = scopeNames ext x

instance (ScopeNames i e t1 t2,ScopeNames i e c1 c2)
      => ScopeNames i e (HsConDeclI i t1 c1) (HsConDeclI (i,e) t2 c2) where
  scopeNames ext d =
    case d of
      HsConDecl s vs ectx c args -> st vs
      HsRecDecl s vs ectx c fields -> st vs
    where
      st vs = exttvs ext vs scAll
      scAll = seqConDecl $ mapConDeclI pairEnv m m d
      m x = scopeNames ext x

instance ScopeNames i e t1 t2
      => ScopeNames i e (TI i t1) (TI (i,e) t2) where
  scopeNames ext t =
      case t of
        HsTyForall vs ps t' -> exttvs ext vs scAll
	_ -> scAll
    where
      scAll = seqTI $ mapTI pairEnv m t
      m x = scopeNames ext x 

freeTyvars tp = [typedTvar i|(i@(HsVar _),_)<-freeNames tp]

typedTvar i = (i,Type blankTypeInfo)
