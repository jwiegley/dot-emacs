module ReAssocBaseStruct where
import BaseSyntax
import ReAssoc
import HsAssoc
--import TypedIds
import DefinedNames
--import DefinedNamesBaseStruct


instance HasInfixApp i (EI i e p ds t c) e where
  infixApp = HsInfixApp
  isInfixApp e =
    case e of
      HsInfixApp e1 op e2 -> Just (e1,op,e2)
      _ -> Nothing

instance HasInfixApp i (PI i p) p where
  infixApp p1 (HsCon c) p2 = HsPInfixApp p1 c p2
  isInfixApp p =
    case p of
      HsPInfixApp p1 op p2 -> Just (p1,HsCon op,p2)
      _ -> Nothing

instance HasInfixDecls i (DI i e p ds t c tp) where
  getInfixDecls d =
    case d of
      HsInfixDecl s f ns -> OperatorEnv [(n,f)|n<-ns]
      _ -> OperatorEnv []

instance HasInfixDecls i ds => HasInfixDecls i (HsModuleI m i ds) where
  getInfixDecls = getInfixDecls . hsModDecls

instance (Eq i,DefinedNames i ds,HasInfixDecls i ds,ReAssoc i ds)
          => ReAssoc i (HsModuleI m i ds) where
  reAssoc env (HsModule s n e i ds) = HsModule s n e i (reAssoc env' ds)
    where env' = extendOps env ds

instance (Eq i,ReAssoc i e,ReAssoc i p,DefinedNames i p,
          HasInfixDecls i ds,ReAssoc i ds,DefinedNames i ds)
	  => ReAssoc i (DI i e p ds t c tp) where
  reAssoc env d =
     case d of
       HsFunBind s ms -> HsFunBind s (map r ms)
       HsPatBind s p rhs ds -> HsPatBind s (reAssoc env p) (r rhs) (r ds)
         where r x = reAssoc env' x
	       env' = rhsOps env p ds
       _ -> mapDI id r r r id id id d
   where r x = reAssoc env x

instance ReAssoc i e => ReAssoc i (HsRhs e) where
  reAssoc = mapRhs . reAssoc

instance (Eq i,HasInfixApp i e e,ReAssoc i e,
	  DefinedNames i p,HasInfixApp i p p,ReAssoc i p,
          ReAssoc i ds,HasInfixDecls i ds,DefinedNames i ds)
          => ReAssoc i (EI i e p ds t c) where
  reAssoc env e =
    case e of
      HsInfixApp e1 op e2 -> reAssocOp env e1 op e2
      HsLet ds e -> HsLet (reAssoc env' ds) (reAssoc env' e)
        where env' = extendOps env ds
      HsLambda ps e -> HsLambda ps (reAssoc env' e)
        where env' = defaultOps env (definedVars ps)
      HsCase e alts -> HsCase (r e) (map r alts)
      HsDo stmts -> HsDo (reAssoc env stmts)
      HsListComp stmts -> HsListComp (reAssoc env stmts)
      _ -> mapEI id r r r id id e
    where r x = reAssoc env x

instance (Eq i,ReAssoc i e,ReAssoc i p,DefinedNames i p,
	  ReAssoc i ds,DefinedNames i ds,HasInfixDecls i ds)
          => ReAssoc i (HsStmt e p ds) where
  reAssoc env stmt =
      case stmt of
	HsGenerator s p e stmt -> HsGenerator s (r p) (r e) (r' stmt)
	  where r' = reAssoc (defaultOps env (definedVars p))
	HsQualifier   e stmt -> HsQualifier (r e) (r stmt)
	HsLetStmt    ds stmt -> HsLetStmt   (r' ds) (r' stmt)
          where r' x = reAssoc (extendOps env ds) x
	HsLast        e      -> HsLast      (r e)
    where r x = reAssoc env x

instance (Eq i,ReAssoc i e,ReAssoc i p,DefinedNames i p,
	  ReAssoc i ds,DefinedNames i ds,HasInfixDecls i ds)
	  => ReAssoc i (HsAlt e p ds) where
  reAssoc env (HsAlt s p rhs ds) = HsAlt s (reAssoc env p) (r rhs) (r ds)
    where
      r x = reAssoc env' x
      env' = rhsOps env p ds

instance (Eq i,ReAssoc i e,ReAssoc i p,DefinedNames i p,
	  ReAssoc i ds,DefinedNames i ds,HasInfixDecls i ds)
	  => ReAssoc i (HsMatchI i e p ds) where
  reAssoc env (HsMatch s n ps rhs ds) =
      HsMatch s n (map (reAssoc env) ps) (r rhs) (r ds)
    where
      r x = reAssoc env' x
      env' = rhsOps env ps ds

rhsOps env p ds = extendOps (defaultOps env (definedVars p)) ds

instance (Eq i,HasInfixApp i p p,ReAssoc i p) => ReAssoc i (PI i p) where
  reAssoc env p =
    case p of
      HsPInfixApp p1 op p2 -> reAssocOp env p1 (HsCon op) p2
      _ -> mapPI id (reAssoc env) p

extendOps env ds = extend2 (defaultOps env ns) (getInfixDecls ds)
  where
    ns = definedValues ds
