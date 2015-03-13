-- $Id: HsDeclMaps.hs,v 1.20 2004/01/22 21:21:46 hallgren Exp $

{-

  Maps for the D functor.

-}

module HsDeclMaps where

import HsDeclStruct
--import HsGuardsStruct
import HsGuardsMaps(mapRhs, accRhs, seqRhs)
import AccList(accList)
import HsIdent
import MUtils


mapDI idf = mapDI2 idf idf

mapDI2 :: (i1 -> i2) ->           -- variable identifier recursion function 
          (i1 -> i2) ->           -- constructor identifier recursion function 
          (e1 -> e2) ->           -- expression recursion function
          (p1 -> p2) ->           -- pattern recursion function
          (d1 -> d2) ->           -- declaration recursion function
          (t1 -> t2) ->           -- type recursion function
          (c1 -> c2) ->           -- context recursion function
          (tp1 -> tp2) ->         -- type pattern recursion function
          DI i1 e1 p1 d1 t1 c1 tp1 -> -- old declaration structure
          DI i2 e2 p2 d2 t2 c2 tp2    -- new declaration structure
mapDI2 vf cf ef pf df tf ctxf tpf decl =
  case decl of
    HsTypeDecl s tp t              -> HsTypeDecl s (tpf tp) (tf t)
    HsNewTypeDecl s cntxt tp cd ns -> HsNewTypeDecl s (ctxf cntxt) (tpf tp)
                                     (mapConDeclI2 vf cf tf ctxf cd) (map cf ns)
    HsDataDecl s cntxt tp cds ns   -> HsDataDecl s (ctxf cntxt) (tpf tp)
                              (map (mapConDeclI2 vf cf tf ctxf) cds) (map cf ns)
    HsClassDecl s c tp fundeps ds   -> HsClassDecl s (ctxf c) (tpf tp)
				                (mapFunDeps vf fundeps) (df ds)
    HsInstDecl s optn c tp ds       -> HsInstDecl s (fmap vf optn) (ctxf c)
						  (tf tp) (df ds)
    HsDefaultDecl s t               -> HsDefaultDecl s (map tf t) 
    HsTypeSig s nms c tp            -> HsTypeSig s (map vf nms) (ctxf c) (tf tp)
    HsFunBind s ms                  -> HsFunBind s 
                                            (map (mapMatchI vf ef pf df) ms) 
    HsPatBind s p rhs ds            -> HsPatBind s (pf p) (mapRhs ef rhs)
                                                                    (df ds)
    HsInfixDecl s fixity names      -> HsInfixDecl s fixity (map (mapHsIdent2 vf cf) names)
    
    -- Hugs compatibility
    HsPrimitiveTypeDecl s cntxt tp  -> HsPrimitiveTypeDecl s (ctxf cntxt) (tpf tp)
    HsPrimitiveBind s nm tp         -> HsPrimitiveBind s (vf nm) (tf tp)

mapMatch = mapMatchI id
mapMatchI vf ef pf df (HsMatch s nm ps rhs ds)
    = HsMatch s (vf nm) (map pf ps) (mapRhs ef rhs) (df ds)

mapConDecl = mapConDeclI id
mapConDeclI idf = mapConDeclI2 idf idf
mapConDeclI2 vf cf tf ctxf (HsConDecl s is c nm bangts)
    = HsConDecl s (map vf is) (ctxf c) (cf nm) (map (mapBangType tf) bangts)
mapConDeclI2 vf cf tf ctxf (HsRecDecl s is c nm nmbangts)
    = HsRecDecl s (map vf is) (ctxf c) (cf nm) (map f nmbangts)
  where
    f (n,bt)    = (map vf n, mapBangType tf bt)
 
mapBangType tf (HsBangedType x)   = HsBangedType (tf x)
mapBangType tf (HsUnBangedType x) = HsUnBangedType (tf x)


{-

   Accumulator for the D functor.

-}

accDI ::(i -> b -> b) ->  -- identifier recursion operator
        (e -> b -> b) ->  -- expression recursion operator
        (p -> b -> b) ->  -- pattern recursion operator
        (d -> b -> b) ->  -- declaration recursion operator
        (t -> b -> b) ->  -- type recursion operator
        (c -> b -> b) ->  -- context recursion operator
        (tp -> b -> b) -> -- type pattern recursion operator
	DI i e p d t c tp ->     -- declaration structure
        b ->              -- base case
        b
accDI idf ef pf df tf cf tpf decl =
    case decl of
    HsTypeDecl s tp t                  -> tpf tp . tf t 
    HsNewTypeDecl s cntxt tp cd names  -> cf cntxt . tpf tp 
                                        . accConDeclI idf tf cf cd 
    HsDataDecl s cntxt tp cds names    -> cf cntxt . tpf tp 
                                        . accList (accConDeclI idf tf cf) cds 
    HsClassDecl s c tp fundeps ds       -> cf c . tpf tp
					. accFunDeps idf fundeps . df ds
    HsInstDecl s optn c tp ds           -> maybe id idf optn . cf c . tf tp . df ds
    HsDefaultDecl s t                   -> accList tf t 
    HsTypeSig s nms c tp                -> accList idf nms . cf c . tf tp 
    HsFunBind s ms                      -> accList (accMatchI idf ef pf df) ms
    HsPatBind s p rhs ds                -> pf p . accRhs ef rhs . df ds
    HsInfixDecl s fixity ns             -> accList (accHsIdent idf) ns

    -- Hugs compatibility
    HsPrimitiveTypeDecl s cntxt tp      -> cf cntxt . tpf tp
    HsPrimitiveBind s nm tp             -> idf nm . tf tp

accD = accDI (curry snd)


accMatch = accMatchI (const id)

accMatchI idf ef pf df (HsMatch s nm ps rhs ds) 
    = idf nm . accList pf ps . accRhs ef rhs . df ds

accConDecl = accConDeclI (const id)

accConDeclI idf tf ctxf (HsConDecl s is c nm bangts) 
    = idf nm . accList idf is . ctxf c . accList (accBangType tf) bangts 
accConDeclI idf tf ctxf (HsRecDecl s is c nm nmbangts) 
    = idf nm . accList idf is . ctxf c . accList f nmbangts 
    where
    f (n,bt) = accList idf n . accBangType tf bt
          
accBangType tf (HsBangedType x) ans   = tf x ans
accBangType tf (HsUnBangedType x) ans = tf x ans        



--- in preparation for the D functor monadic trifecta 

seqDI :: (Functor m,Monad m) =>
        -- declaration structure containing computations:
        DI(m i)
          (m e)     --   ... delivering expression recursion
          (m p)     --   ... delivering pattern recursion
          (m d)     --   ... delivering declaration recursion
          (m t)     --   ... delivering type recursion
          (m c)     --   ... delivering context recursion
          (m tp) -> --   ... delivering type pattern recursion
        m (DI i e p d t c tp) -- computation delivering declaration structure
seqDI decl =
    case decl of
    HsTypeDecl s tp t           -> HsTypeDecl s # tp <# t
    HsNewTypeDecl s c tp cd nms ->
        HsNewTypeDecl s # c <# tp <# seqConDecl cd <# sequence nms
    HsDataDecl s c tp cds nms   ->
        HsDataDecl s # c <# tp <# mapM seqConDecl cds <# sequence nms
    HsClassDecl s c tp fundeps ds -> HsClassDecl s # c <# tp <# seqFunDeps fundeps <# ds
    HsInstDecl s optn c tp ds   -> HsInstDecl s # seqMaybe optn <# c <# tp <# ds
    HsDefaultDecl s t            -> HsDefaultDecl s # sequence t
    HsTypeSig s nms c tp         -> HsTypeSig s # sequence nms <# c <# tp
    HsFunBind s ms               -> HsFunBind s # mapM seqMatch ms
    HsPatBind s p rhs ds         -> HsPatBind s # p <# seqRhs rhs <# ds
    HsInfixDecl s fixity names   -> HsInfixDecl s fixity # mapM seqHsIdent names

    HsPrimitiveTypeDecl s c tp   -> HsPrimitiveTypeDecl s # c <# tp
    HsPrimitiveBind s nm tp      -> HsPrimitiveBind s # nm <# tp
            

seqConDecl (HsConDecl sloc is c name bangtypes) = 
  HsConDecl sloc # sequence is <# c <# name <# mapM seqBangType bangtypes
seqConDecl (HsRecDecl sloc is c name fields) = 
  HsRecDecl sloc # sequence is <# c <# name <# mapM (sequence >#< seqBangType) fields

--mapSndM seqBangType fields


seqBangType (HsBangedType t)   = HsBangedType # t
seqBangType (HsUnBangedType t) = HsUnBangedType # t

seqMatch (HsMatch sloc name bs rhs c) = 
  HsMatch sloc # name <# sequence bs <# seqRhs rhs <# c


mapFunDeps = map . mapFunDep
mapFunDep = apBoth . map

accFunDeps = accList . accFunDep

accFunDep tf (ts1,ts2) = accList tf ts1 . accList tf ts2

seqFunDeps fs = mapM seqFunDep fs
seqFunDep fd = sequence>#<sequence $ fd
