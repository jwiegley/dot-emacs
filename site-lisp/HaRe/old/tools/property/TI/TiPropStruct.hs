module TiPropStruct where
import PropSyntax hiding (Q(..))
import qualified PropSyntax as P(Q(..))
import PropSyntaxStruct(Prop,prop)
import TI hiding (TI)
--import TiHsName
--import TiT(kcStar,kcPred)
import TiE(tcLambda')
import TiPrelude(pt)
import SrcLoc
import TypedIds(HasIdTy)
import MUtils
import Monad(unless)
import PrettySymbols(el)
import PrettyPrint hiding (var)
import SimpleGraphs(reachable')

-- For debugging:
--import IOExts(trace)

-- I wish there was an easier way to declare instances in Haskell...

instance (TypeCheck i be e,TypeCheck i pe e) => TypeCheck i (Prop be pe) e where
  tc = prop tc tc
{-
instance (Printable bd,Printable pd,
          TypeCheckDecl i bd d,TypeCheckDecl i pd d)
       => TypeCheckDecl i (Prop bd pd) d where
  tcDecl bs d = --trace (pp d)  $
                prop (tcDecl bs) (tcDecl bs) d

instance (Fresh i,TypeId i,ValueId i,TypeVar i,HasSrcLoc i,--HasIdTy i,
          Printable i,Printable pa,Printable pp,
          TypeCheck i pa (Typed i pa2),
          TypeCheck i pp (Typed i pp2),
	  HasDef ds2 d2,
	  HasPropStruct d2 (PD i pa2 pp2))
      => TypeCheckDecl i (PD i pa pp) ds2
  where tcDecl = tcPD
-}
instance (TypeId i,ValueId i,Fresh i,HasSrcLoc i,HasIdTy x i,
          Printable i,Printable e1,--Printable t,
	  TypeCheck i e1 (Typed i e2),
	  TypeCheck i pa1 (Typed i pa2),
	  TypeCheck i pp1 (Typed i pp2),
	  HasTypeAnnot i e2,HasId i e2,
	  HasPropStruct r (PA i e2 (HsQualTypeI i) pa2 pp2))
      => TypeCheck i (PA i e1 (HsQualTypeI i) pa1 pp1) (Typed i r)
  where tc = tcPA

instance (TypeId i,ValueId i,Fresh i,HasSrcLoc i,HasIdTy x i,
          Printable t,Printable e1,Printable p1,
	  Printable pa1,Printable pp1,PrintableOp i,
	  DefinedNames i p1,
          TypeCheck i e1 (Typed i e2),
          TypeCheck i p1 (Typed i p2),
	  TypeCheck i pa1 (Typed i pa2),
	  TypeCheck i pp1 (Typed i pp2),
	  HasId i e2,
	  HasBaseStruct t (TI i t'),
	  HasPropStruct r (PP i e2 p2 (P.Q [t] (Type i)) pa2 pp2)) =>
         TypeCheck i (PP i e1 p1 (P.Q [t] (Type i)) pa1 pp1) (Typed i r)
  where tc = tcPP

{-
predAp i [] = predId i
predAp i as = predApp i as
-}
targs vs = map (([]P.:=>).tyvar) vs

tcPP p =
  case p of
--  PredId q -> do t <- propinst q
--		   predId q>:t
{-
    PredId q -> do (_,ds):>:t <- propinst_loc q -- add type params!!
                   predAp q (map Left ds)>:t
-}
    PredApp i [] es -> do ((sc,vs),ds):>:ti <- propinst_loc i
		          es':>:ts <- unzipTyped # mapM tcArg es
		          v <- pfresh
		          ti=:=funT (ts++[v])
		          tpredApp i (targs vs) (map Left ds++es') >: v
    PredArrow p1 p2 -> do p1':>:t1 <- tcPred p1
			  p2':>:t2 <- tcPred p2
			  predArrow p1' p2'>:tPred (funT [t1,t2])
    PredInfixApp p1 i p2 -> do ((sc,vs),ds):>:ti <- propinst_loc i
                               p1':>:t1 <- tc p1
			       p2':>:t2 <- tc p2
		               v <- pfresh
		               ti=:=funT [t1,t2,v]
			       let p' = if null ds && null vs
			                then predInfixApp p1' i p2'
				        else tpredApp i (targs vs) (map Left ds++map Right [p1',p2'])
			       p'>:v
    PredNeg optt p -> do p':>:t <- tc p
			 checkOptT optt t
		         predNeg (Just ([]P.:=>t)) p'>:t
    PredOp op optt p1 p2 -> tcBinPred (predOp op) optt p1 p2
    PredLfp i optt p -> tcFp predLfp' i optt p
    PredGfp i optt p -> tcFp predGfp' i optt p
    PredNil -> do v<-tfresh
		  listType <- getListType
                  predNil>:tPred (listType v)
    PredLifted e -> do e':>:t <- tc e
		       v <- tfresh
		       tBool <- getBoolType
		       t=:=funT [v,tBool]
		       predLifted e'>:tPred v
    PredStrong p -> do p':>:t <- tc p
		       isPred t
		       predStrong p'>:t

    PredParen p -> emap predParen # tc p
    PredComp pts a -> do let (ps,ts) = unzip pts
		             --ts' = ts -- repeat Nothing -- hmm!!
		         (ps',a') :>: (tps,t') <- tcLambda' ps a
			 isProp t'
			 let tps' = [Just ([]P.:=>tp)|tp<-tps]
			 {- No rank 2 polymorphism: type variables in the
			    type signatures are treated as free type variables
			    that can be unified with other types. The type
			    signature can only be used to make the
			    inferred type more specific, not more general. -}
			 sequence_ [tp=:=t|(tp,Just (_ P.:=>t))<-zip tps ts]--hm
			 predComp (zip ps' tps') a'>:tPredn tps
    _ -> error (pp p)

tcArg a = either (\e->emap Left # tc e) (\p->emap Right # tc p) a

tcFp f i optt p =
    do --v <- pfresh -- too general (ok if proper kind checking is done)
       vv <- tfresh
       let v = tPred vv -- restricted to unary predicates
       p':>:t <-extend1 (HsCon i) (mono v) (tc p)
       t=:=v
       checkOptT optt v
       let qv= []P.:=>vv -- vv is more appropriate than v in the Alfa transl
       f i qv p'>:t

checkOptT optt v =
    case optt of
      Nothing -> done
      Just ([]P.:=>ta) -> ta=:=v
      _ -> fail "qualified type annotation not supported"


----

tProp :: TypeCon i => Type i
tProp = pt "Prop"
tPred v = funT [v,tProp]
tPredn ts = funT (ts++[tProp])

isProp t = t=:=tProp

tcProp a = do a':>:t <- tc a
              isProp t
	      return a'

tcPred a = do ta@(a':>:t) <- tc a
              t'<-isPred t
	      a'>:t' -- hmm

isPred t = do v <- tfresh
              t=:=tPred v
	      return v

tcBinProp op a1 a2 = do p' <- propOp op # tcProp a1 <# tcProp a2
		        p'>:tProp

tcBinPred op optt p1 p2 = do p1':>:t1 <- tc p1
			     p2':>:t2 <- tc p2
			     t1=:=t2
			     checkOptT optt t1 -- hmm
			     op (Just ([]P.:=>t1)) p1' p2'>:t1

propAp i [] = propId i
propAp i es = propApp i es

tcPA pa =
  case pa of
    Quant q i optt pa ->
       do t <- tfresh
	  let bs = [HsVar i:>:t]
	  --bs <- intro [HsVar i]
	  check t optt
          pa' <- extendts ((map.fmap) mono bs) $ tcProp pa
          --quant q i optt pa' >: tProp
	  quant q i (Just ([] P.:=> t)) pa' >: tProp
      where
       check t (Just (_ P.:=>t')) = t=:=t' -- !!
       check _ _ = return ()

--  PropId q -> do t <- propinst q
--		   propId q>:t
{-
    PropId q -> do (_,ds):>:t <- propinst_loc q -- add type params!!
                   propAp q ds>:t
-}
    PropApp i [] es -> do ((sc,vs),ds):>:ti <- propinst_loc i
		          es':>:ts <- unzipTyped # mapM tcArg es
		          v <- pfresh
		          ti=:=funT (ts++[v])
		          tpropApp i (targs vs) (map Left ds++es') >: v
    PropNeg a -> do a' <- tcProp a; propNeg a' >: tProp
    PropOp op a1 a2 -> tcBinProp op a1 a2
    PropEqual e1 e2 -> do e1':>:t1 <- tc e1
			  e2':>:t2 <- tc e2
			  t1=:=t2
			  propEqual (typeAnnot e1' t1) e2' >: tProp
    PropHas e p -> do e':>:te <- tc e
		      p':>:tp <- tc p
		      tp=:=funT [te,tProp]
		      propHas e' p' >: tProp
    PropParen a -> emap propParen # tc a

tcPD bs d =
  case d of
    HsAssertion s optn pa ->
       posContext' s "in assertion" $
       do pa' <- tcProp pa
	  maybe done (isProp @@ coninst' bs) optn
	  return $ oneDef $ hsAssertion s optn pa'
    HsPropDecl s n ns pp ->
       do lbs <- ptintro ns
	  tn <- coninst' bs n
	  pp':>:t <- extendts ((map.fmap) mono lbs) $ tc pp
	  tn=:=funT ([ t | _:>:t<-lbs]++[t])
          return $ oneDef $ hsPropDecl s n ns pp'

ptintro xs = do ts <- freshlist (length xs)
		let lbs = zipTyped (xs:>:ts)
	        addptypes lbs
	        return lbs

addptypes ts = mapM_ addptype ts
addptype (HsVar _:>:t) = addtype t
addptype (HsCon _:>:t) = addprop t

coninst' bs n =
  case [ t | HsCon x:>:t<-bs,x==n] of
    t:_ -> return t
    _ -> fail$"Type checker bug: no type introduced for: "++pp n

{-
propinst x =
  do s <- sch (HsCon x)
     ctx :=> t <- sinst s
     unless (null ctx) $
       fail.pp $
	 sep [srcLoc x<+>"overloaded predicates are not supported (yet):",
	      nest 4 (x<+>el<+>s)]
     return (toPredType (isCon x) t)
-}

propinst_loc x = propinst_loc' (Just (srcLoc x)) x
propinst_loc' s x =
  do sc@(Forall ags gs qt) <- sch (HsCon x)
     vs <- freshvars gs
     let ctx:=> t = freshen' vs (tdom gs) qt
     ds <- newdicts s ctx
     ((sc,{-map tyvar-} vs),map var ds) >: toPredType (isCon x) t

toPredType False = id
toPredType True  = liftCon

liftCon x = funT . map tPred . flatFunT $ x

flatFunT t =
  case isFunT t of
    Just (t1,t2) -> t1:flatFunT t2
    _ -> [t]

pfresh = do t <- fresh
	    addprop t
	    return t

addprop t = addkinst (t:>:kprop)

{-+
Predicate definition can not use explicit recursion. The Gfp & Lfp operators
have to be used instead.
-}
checkPredicateRec ds =
    unless (null recpreds) $ 
      declContext recpreds $
        fail "Recursive predicates"
  where
    recpreds = [pred|(pred,_)<-g,pred `elem` reachable' g [pred]]
    g = [(i,free) | Just d@(HsPropDecl {})<-map propstruct ds,
	            let free=freeValueNames d,
	            i<-definedValueNames d]
