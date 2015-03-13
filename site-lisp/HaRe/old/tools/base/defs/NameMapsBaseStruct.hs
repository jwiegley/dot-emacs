module NameMapsBaseStruct where
import NameMaps
import BaseSyntax
import HasBaseName
import MUtils
import DefinedNames -- because of tp, grr

--accNamesModule f (HsModule s m e i ds) = HsModule s m e i (accNames f ds)

instance (AccNames i e,AccNames i p,AccNames i ds, AccNames i t, AccNames i c)
       => AccNames i (EI i e p ds t c) where
  accNames f = accEI f m m m m m
    where m x = accNames f x

instance AccNames i p => AccNames i (PI i p) where
  accNames f = accPI f (accNames f)

instance (AccNames i e, AccNames i p, AccNames i ds, AccNames i t, AccNames i c,
	  AccNames i tp)
       => AccNames i (DI i e p ds t c tp) where
  accNames f = accDI f m m m m m m
    where m x = accNames f x

instance AccNames i t => AccNames i (TI i t) where
  accNames f = accTI f (accNames f)

instance AccNames i (HsIdentI i) where accNames = accHsIdent

-----------------------------------------------------------------------------
mapNamesModule2 d f (HsModule s mn e i ds) =
    HsModule s mn (m2 e) (m2 i) (m2 ds)
  where
    m2 x = mapNames2 d f x

{-
-- This could be error prone...
instance MapNames i1 (HsIdentI i1) i2 (HsIdentI i2) where
  mapNames = fmap
  --mapNames2  = ?? -- unknown namespace
-}

instance (HasBaseName m ModuleName, MapNames i1 ds1 i2 ds2)
      => MapNames i1 (HsModuleI m i1 ds1) i2 (HsModuleI m i2 ds2) where
  mapNames2 = mapNamesModule2

instance MapNames i1 (HsExportSpecI m i1) i2 (HsExportSpecI m i2) where
  mapNames2 dctx f@(vf,cf) e =
    case e of
      ModuleE mn -> ModuleE mn
      EntE e -> EntE (mapNames2 Export f e)

instance MapNames i1 (EntSpec i1) i2 (EntSpec i2) where
  mapNames2 dctx f@(vf,cf) e =
    -- pre: dctx==Export || dctx==Import m
    case e of
      Var i -> Var (vf eval i)
      Abs i -> Abs (cf etype i)
      AllSubs i -> AllSubs (cf etype i)
      ListSubs i is -> ListSubs (cf etype i) (map (subent i) is)
    where
      eval = (prim,ValueNames)
      etype = (prim,ClassOrTypeNames)
      subent i = both (sub i,ValueNames) mapHsIdent2 f

      prim = ent dctx Nothing
      sub  = ent dctx . Just

      ent Export = ExpEnt
      ent (Import m) = ImpEnt m
      ent _ = const Use -- entity specification in unexpected context!!

instance HasBaseName m ModuleName => 
         MapNames i1 (HsImportDeclI m i1) i2 (HsImportDeclI m i2) where
  mapNames2 dctx f (HsImportDecl s m q as optspec) =
      HsImportDecl s m q as (fmap (apSnd (mapNames2 d f)) optspec)
    where d = Import (getBaseName m)

instance (MapNames i1 e1 i2 e2,
	  MapNames i1 p1 i2 p2,
	  MapNames i1 ds1 i2 ds2,
	  MapNames i1 t1 i2 t2,
	  MapNames i1 c1 i2 c2)
       => MapNames i1 (EI i1 e1 p1 ds1 t1 c1)
		   i2 (EI i2 e2 p2 ds2 t2 c2) where
  mapNames2 dctx f e =
      case e of
        HsRecConstr s i fs -> HsRecConstr s (snd f useval i) (m fs)
        HsRecUpdate s e fs -> HsRecUpdate s (m e) (m fs)
        _ -> bothval mapEI2 f m mp ml ml ml e
    where
      m x = m' dctx x
      ml x = m' Local x
      mp x = m' Pattern x
      m' dctx = mapNames2 dctx f

instance MapNames i1 p1 i2 p2 => MapNames i1 (PI i1 p1) i2 (PI i2 p2) where
  mapNames2 dctx f@(vf,cf) p =
    case p of
      HsPRec i p -> HsPRec (snd f useval i) (m p)
      _ -> mapPI2 vf' (cf useval) m p
    where
      m x = mapNames2 dctx f x
      --vf' = vf (defval dctx)
      vf' = case dctx of ClassDef _ -> vf useval
			 _ -> vf (defval dctx)

instance MapNames i1 e1 i2 e2
      => MapNames i1 (HsFieldI i1 e1) i2 (HsFieldI i2 e2) where
  mapNames2 dctx f = mapFieldI (fst f (FieldLabel,ValueNames)) m
    where
      m = mapNames2 dctx f

-- All identifiers i in EI i ... and PI i p denote values
-- All identifiers i in TI i t denote types 

instance (MapNames i1 e1 i2 e2,
	  MapNames i1 p1 i2 p2,
	  MapNames i1 ds1 i2 ds2,
	  MapNames i1 t1 i2 t2,
	  MapNames i1 c1 i2 c2,
	  MapNames i1 tp1 i2 tp2,
	  DefinedNames i1 t1,
	  DefinedNames i1 tp1)
       => MapNames i1 (DI i1 e1 p1 ds1 t1 c1 tp1)
		   i2 (DI i2 e2 p2 ds2 t2 c2 tp2) where
  mapNames2 dctx f@(vf,cf) d =
      case d of
        HsTypeDecl s tp t -> HsTypeDecl s (m tp) (ml t)
        HsNewTypeDecl s ctx tp cd ns ->
             HsNewTypeDecl s (ml ctx) (m tp) (map2conD cd) (map tconf ns)
        HsDataDecl s ctx tp cds ns  ->
             HsDataDecl s (ml ctx) (m tp) (map map2conD cds) (map tconf ns)
	HsClassDecl s ctx tp fdeps ds ->
	    HsClassDecl s (ml ctx) (m tp) (mapFunDeps tvarf fdeps) (mc c1 ds)
	  where c1 = definedType tp 
        HsInstDecl s optn ctx tp ds ->
	     HsInstDecl s (fmap vdef optn) (ml ctx) (ml tp) (mi c1 ds)
	  where c1 = definedType tp 
		--c2 = tconf c1
	HsDefaultDecl s ts -> HsDefaultDecl s (ml ts)
	HsTypeSig s is ctx tp -> HsTypeSig s (map vf is) (ml ctx) (ml tp)
          where
	    vf = case dctx of ClassDef _ -> vdef
	                      _          -> vsig
	HsInfixDecl s fixity is ->
            HsInfixDecl s fixity (map (bothsigval mapHsIdent2 f) is)
        HsFunBind s ms -> HsFunBind s (m ms)
        HsPrimitiveTypeDecl s ctx tp  ->
            HsPrimitiveTypeDecl s (ml ctx) (m tp)
	HsPrimitiveBind s i tp -> HsPrimitiveBind s (vdef i) (ml tp)
        _ -> bothval mapDI2 f m m ml m m m d
    where
      m x = m' dctx x
      mc c x = m' (ClassDef c) x
      mi c x = m' (Instance c) x
      ml x = m' Local x
      m' dctx = mapNames2 dctx f
      tconf = cf usetype
      tvarf = vf usetype
      --vuse = vf useval
      vdef  = vf (defval dctx)
      vsig  = vf (sigval dctx)
      cdef  = cf (defval dctx)
      --bothdefval = both (defval dctx)
      bothsigval = both (sigval dctx)

      map2conD (HsConDecl s is c n args) =
          HsConDecl s (localq f is) (ml c) (cdef n) (ml args)
      map2conD (HsRecDecl s is c n fields) =
          HsRecDecl s (localq f is) (ml c) (cdef n) (map mf fields)
        where
          mf (is,t) = (map vdef is,ml t)

instance MapNames i1 t1 i2 t2
      => MapNames i1 (HsBangType t1) i2 (HsBangType t2) where
  mapNames2 dctx f = mapBangType (mapNames2 dctx f)

instance (MapNames i1 e1 i2 e2,
	  MapNames i1 p1 i2 p2,
	  MapNames i1 ds1 i2 ds2)
       => MapNames i1 (HsMatchI i1 e1 p1 ds1)
		   i2 (HsMatchI i2 e2 p2 ds2) where
  mapNames2 dctx f@(vf,_) (HsMatch s n ps rhs ds) =
      HsMatch s (vf' n) (mp ps) (mapRhs m rhs) (ml ds)
    where
      vf' = case dctx of ClassDef _ -> vuse
			 --Instance _ -> vdef
			 _ -> vdef
      m x = m' dctx x
      ml x = m' Local x
      mp x = m' Pattern x
      m' dctx = mapNames2 dctx f
      vdef = vf (defval dctx)
      vuse = vf useval

{-+
The TI structure is used for both lhss of type definitions and for type
expressions. We set the context to Local when entering a type expression,
and to TopLevel when entering the lhs of a type defintion.
-}
instance MapNames i1 t1 i2 t2 => MapNames i1 (TI i1 t1) i2 (TI i2 t2) where
  mapNames2 dctx f@(vf,cf) t =
      case t of
        HsTyForall vs ps t' -> HsTyForall (localq f vs) (m ps) (m t')
        _ -> mapTI2 vf' cf' (mapNames2 dctx f) t
    where
      m x = mapNames2 dctx f x

      (vf',cf') = case dctx of
		    Local -> (vf usetype,cf usetype)
		    _     -> (vf (deftype Pattern),cf (deftype dctx))

localq (vf,_) = map (vf (deftype Pattern))

--------------------------------------------------------------------------------

instance SeqNames m ds1 ds2
      => SeqNames m (HsModuleI mn (m i) ds1) (HsModuleI mn i ds2) where
  seqNames (HsModule s m e i ds) =
     HsModule s m # seqNames e <# seqNames i <# seqNames ds

instance (Functor m,Monad m) => SeqNames m (EntSpec (m i)) (EntSpec i) where
  seqNames = seqEntSpec

instance (Functor m,Monad m)
      => SeqNames m (HsImportDeclI mn (m i)) (HsImportDeclI mn i) where
  seqNames = seqImportDecl

instance (Functor m,Monad m)
      => SeqNames m (HsExportSpecI mn (m i)) (HsExportSpecI mn i) where
  seqNames = seqExportSpec

instance (SeqNames m e1 e2,SeqNames m p1 p2,SeqNames m ds1 ds2,
          SeqNames m t1 t2,SeqNames m c1 c2)
      => SeqNames m (EI (m i) e1 p1 ds1 t1 c1) (EI i e2 p2 ds2 t2 c2) where
  seqNames = seqEI . mapEI id sn sn sn sn sn

instance SeqNames m p1 p2 => SeqNames m (PI (m i) p1) (PI i p2) where
  seqNames = seqPI . mapPI id sn

instance (SeqNames m e1 e2,SeqNames m p1 p2,SeqNames m ds1 ds2,
          SeqNames m t1 t2,SeqNames m c1 c2,SeqNames m tp1 tp2)
      => SeqNames m (DI (m i) e1 p1 ds1 t1 c1 tp1) (DI i e2 p2 ds2 t2 c2 tp2) where
  seqNames = seqDI . mapDI id sn sn sn sn sn sn

instance SeqNames m t1 t2 => SeqNames m (TI (m i) t1) (TI i t2) where
  seqNames = seqTI . mapT sn

r x = return x
sn x = seqNames x
--------------------------------------------------------------------------------
